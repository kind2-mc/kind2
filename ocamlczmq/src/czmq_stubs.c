#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

#include <zmq.h>
#include <czmq.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/intext.h>
#include <caml/threads.h>

/******************
 * Error handling *
 ******************/
 
 // This section from https://github.com/pdhborges/ocaml-zmq/blob/master/src/fail.c

/* This table must be synchronized with the variant definition. */
static int const caml_zmq_error_table[] = {
    EINVAL,
    EFAULT,
    EMTHREAD,
    ETERM,
    ENODEV,
    EADDRNOTAVAIL,
    EADDRINUSE,
    ENOCOMPATPROTO,
    EPROTONOSUPPORT,
    EAGAIN,
    ENOTSUP,
    EFSM,
    ENOMEM,
    EINTR
};

/* This must be the last value of the variant. */
static int const caml_zmq_EUNKNOWN =
    (sizeof caml_zmq_error_table) / (sizeof caml_zmq_error_table[0]);

void caml_zmq_raise_if(int condition) {
    CAMLparam0();
    CAMLlocalN(error_parameters, 2);
    if (condition) {
        int error_to_raise = caml_zmq_EUNKNOWN;
        int current_errno = zmq_errno();
        int i;
        for (i = 0; i < caml_zmq_EUNKNOWN; i++) {
            if (current_errno == caml_zmq_error_table[i]) {
                error_to_raise = i;
                break;
            }
        }     
        error_parameters[0] = Val_int(error_to_raise);
        error_parameters[1] = caml_copy_string(zmq_strerror(current_errno));
        caml_raise_with_args( *caml_named_value("zmq exception"),
                                2, error_parameters);
    }
    CAMLreturn0;
}

/******************
 *  zctx          *
 ******************/

#define CAML_CZMQ_zctx_val(v) (zctx_st *) Data_custom_val(v)

// keep track of sockets on a context 
typedef struct _zctx_st {
    zctx_t *context;
    int socket_count;
    bool is_freed;
} zctx_st;

void caml_czmq_finalize_zctx(value context_val)
{
    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);

    if (context_record->socket_count == 0) { 
        zctx_destroy( &(context_record->context) ); 
    } else {
        // socket still using context; socket now responsible for destroying it
        context_record->is_freed = true;
    }
}

static struct custom_operations caml_czmq_zctx_ops = {
    identifier:     "org.czmq.zctx",
    finalize:       caml_czmq_finalize_zctx,
    compare:        custom_compare_default,
    hash:           custom_hash_default,
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};

static value caml_czmq_copy_zctx( zctx_st *context ) {
    CAMLparam0 ();
    CAMLlocal1 (context_val);

    context_val = caml_alloc_custom(&caml_czmq_zctx_ops, sizeof(zctx_st), 0, 1);
    memcpy( Data_custom_val(context_val), context, sizeof(zctx_st) );
    
    CAMLreturn (context_val);
}


CAMLprim value 
caml_zctx_new(value unit)
{
    CAMLparam0 ();
    CAMLlocal1 (context_val);

    void *context = zctx_new();
    assert (context);
    zctx_st context_record;
    context_record.context = context;
    context_record.socket_count = 0;
    context_record.is_freed = false;
    context_val = caml_czmq_copy_zctx(&context_record);
    
    CAMLreturn (context_val);
}

CAMLprim value 
caml_zctx_set_iothreads(value context_val, value threads_val) 
{
    CAMLparam2 (context_val, threads_val);

    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);
    int threads = Int_val(threads_val);
    zctx_set_iothreads(context_record->context, threads);
    
    CAMLreturn (Val_unit);
}

CAMLprim value 
caml_zctx_set_linger(value context_val, value linger_val) 
{
    CAMLparam2 (context_val, linger_val);
    
    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);
    int linger = Int_val(linger_val);
    zctx_set_iothreads (context_record->context, linger);
    
    CAMLreturn (Val_unit);
}

// need to take a closer look at these ctx options;
// hwm not reporting changes made via set_hwm
CAMLprim value 
caml_zctx_set_hwm(value context_val, value hwm_val) 
{
    CAMLparam2 (context_val, hwm_val);
    
    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);
    int hwm = Int_val(hwm_val);
    zctx_set_hwm(context_record->context, hwm);
    
    CAMLreturn (Val_unit);
}

CAMLprim value 
caml_zctx_hwm(value context_val) 
{
    CAMLparam1 (context_val);
    
    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);
    int hwm = zctx_hwm(context_record->context);

    CAMLreturn (Val_int(hwm));
}


/******************
 *  zsocket       *
 ******************/

// a socket type containing a zsocket pointer and a zctx_st pointer,
// both of which are needed for the socket finalizer
 typedef struct _socket_st {
    void *socket;
    zctx_st *context_record;
} socket_st;

#define CAML_CZMQ_zsocket_val(v) (socket_st *) Data_custom_val(v)

void caml_czmq_finalize_zsocket(value socket_val)
{
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);

    zsocket_destroy(socket_record->context_record->context, 
                    socket_record->socket);

    if ( --(socket_record->context_record->socket_count) == 0 ) {
        /* this is the last socket on the context. destroy context 
            if already freed on the OCaml side */
        if (socket_record->context_record->is_freed == true) { 
            zctx_destroy( &(socket_record->context_record->context) );
        }
    }
}

static struct custom_operations caml_czmq_zsocket_ops = {
    identifier:     "org.czmq.zsocket",
    finalize:       caml_czmq_finalize_zsocket,
    compare:        custom_compare_default,
    hash:           custom_hash_default,
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};

static value caml_czmq_copy_zsocket( socket_st *socket_record ) {
    CAMLparam0 ();
    CAMLlocal1 (socket_val);

    socket_val = caml_alloc_custom(&caml_czmq_zsocket_ops, sizeof(socket_st), 0, 1);
    memcpy( Data_custom_val(socket_val), socket_record, sizeof(socket_st) );
    
    CAMLreturn (socket_val);
}


CAMLprim value 
caml_zsocket_new(value context_val, value type_val)
{
    CAMLparam2 (context_val, type_val);
    CAMLlocal1 (socket_val);

    zctx_st *context_record = CAML_CZMQ_zctx_val(context_val);
    int type = Int_val(type_val);
    // create socket
    void *socket = zsocket_new ( context_record->context, type );
    assert (socket);
    context_record->socket_count++;
    // return structure of zctx and zsocket pointers
    socket_st socket_record;
    socket_record.socket = socket;
    socket_record.context_record = context_record;
    socket_val = caml_czmq_copy_zsocket(&socket_record);
    
    CAMLreturn (socket_val);
}

CAMLprim value 
caml_zsocket_bind(value socket_val, value address_val)
{
    CAMLparam2 (socket_val, address_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *address = String_val(address_val);
    int rc = zsocket_bind(socket_record->socket, address);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value 
caml_zsocket_connect(value socket_val, value address_val)
{
    CAMLparam2 (socket_val, address_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *address = String_val(address_val);
    int rc = zsocket_connect(socket_record->socket, address);

    CAMLreturn (Val_int(rc));
}

/******************
 *  zsocketopt  *
 ******************/

CAMLprim value 
caml_zsocket_set_subscribe(value socket_val, value string_val)
{
    CAMLparam2 (socket_val, string_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = String_val(string_val);
    zsocket_set_subscribe(socket_record->socket, string);

    CAMLreturn (Val_unit);
}


CAMLprim value 
caml_zsocket_set_unsubscribe(value socket_val, value string_val)
{
    CAMLparam2 (socket_val, string_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = String_val(string_val);
    zsocket_set_unsubscribe(socket_record->socket, string);

    CAMLreturn (Val_unit);
}


/******************
 *  zstring       *
 ******************/

CAMLprim value
caml_zstr_recv(value socket_val)
{
    CAMLparam1 (socket_val);
    CAMLlocal1 (string_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = zstr_recv(socket_record->socket);
    string_val = caml_copy_string(string);
    free(string);
    
    CAMLreturn (string_val);
}

CAMLprim value
caml_zstr_recv_nowait(value socket_val)
{
    CAMLparam1 (socket_val);
    CAMLlocal1 (string_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = zstr_recv_nowait(socket_record->socket);
    if (string) {
        string_val = caml_copy_string(string);
        free(string);
        CAMLreturn (string_val);
    }

    // no string recieved
    CAMLreturn (caml_copy_string(""));
}

CAMLprim value
caml_zstr_send(value socket_val, value string_val)
{
    CAMLparam2 (socket_val, string_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = String_val(string_val);
    int rc = zstr_send(socket_record->socket, string);

    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zstr_sendm(value socket_val, value string_val)
{
    CAMLparam2 (socket_val, string_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    char *string = String_val(string_val);
    int rc = zstr_sendm(socket_record->socket, string);

    CAMLreturn (Val_int(rc));
}

/******************
 *  zframe        *
 ******************/

#define CAML_CZMQ_zframe_val(v) (*(void **) Data_custom_val(v))

void caml_czmq_finalize_zframe(value frame_val)
{
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    zframe_destroy(&frame);   
}

static struct custom_operations caml_czmq_zframe_ops = {
    identifier:     "org.czmq.zframe",
    finalize:       caml_czmq_finalize_zframe,
    compare:        custom_compare_default,
    hash:           custom_hash_default,
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};

static value caml_czmq_copy_zframe(void **zframe) {
    CAMLparam0 ();
    CAMLlocal1 (frame_val);

    frame_val = caml_alloc_custom(&caml_czmq_zframe_ops, 
                                    sizeof(void *), 0, 1);
    memcpy( Data_custom_val(frame_val), zframe, sizeof(void *) );   
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zframe_new(value data_val, value size_val)
{
    CAMLparam2 (data_val, size_val);
    CAMLlocal1 (frame_val);

    // copy bytes from ocaml array to a c array    
    int size = Int_val(size_val); 
    unsigned char bytes[size];
    int i;
    for (i = 0; i < size; i++) 
    { 
        bytes[i] = Byte(data_val, i); 
    }
    // give c array to zframe constructor
    void *frame = zframe_new(bytes, size);
    caml_zmq_raise_if(frame == NULL);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zframe_getbytes(value frame_val)
{
    CAMLparam1(frame_val);
    CAMLlocal1(bytes);

    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    size_t size = zframe_size(frame);

    // copy data to a new ocaml array
    bytes = caml_alloc(size, 0);
    unsigned char *dataptr = zframe_data(frame);
    int i;
    for (i = 0; i < size; i++) 
    {
        Store_field(bytes, i, Val_int(dataptr[i]));
    }
    CAMLreturn( bytes );
}

CAMLprim value
caml_zframe_recv(value socket_val)
{
    CAMLparam1 (socket_val);
    CAMLlocal1 (frame_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    void *frame = zframe_recv(socket_record->socket);
    caml_zmq_raise_if(frame == NULL);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zframe_send(value frame_val, value socket_val, value flags_val)
{
    CAMLparam3 (frame_val, socket_val, flags_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    int flags = Int_val(flags_val);
    int rc = zframe_send(&frame, socket_record->socket, flags);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zframe_size(value frame_val)
{
    CAMLparam1 (frame_val);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    size_t size = zframe_size(frame);
    
    CAMLreturn (Val_int(size));
}

CAMLprim value
caml_zframe_dup(value orig_frame_val)
{
    CAMLparam1 (orig_frame_val);
    CAMLlocal1 (new_frame_val);
    
    zframe_t *orig_frame = CAML_CZMQ_zframe_val(orig_frame_val);
    void *new_frame = zframe_dup(orig_frame);
    caml_zmq_raise_if(new_frame == NULL);
    new_frame_val = caml_czmq_copy_zframe(&new_frame);
    
    CAMLreturn (new_frame_val);
}

CAMLprim value
caml_zframe_strhex(value frame_val)
{
    CAMLparam1 (frame_val);
    CAMLlocal1 (string_val);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    char *string = zframe_strhex(frame);
    string_val = caml_copy_string(string);
    free (string);
    
    CAMLreturn (string_val);
}


CAMLprim value
caml_zframe_strdup(value frame_val)
{
    CAMLparam1(frame_val);
    CAMLlocal1(bytes);

    // this is done manually to support binary strings
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    size_t size = zframe_size(frame);
    char *dataptr = zframe_data(frame);
    // copy data to a new ocaml string
    bytes = caml_alloc_string(size);
    memcpy( String_val(bytes), dataptr, size);

    CAMLreturn( bytes );
}




CAMLprim value
caml_zframe_streq(value zframe_val, value string_val)
{
    CAMLparam2 (zframe_val, string_val);
    CAMLlocal1 (boolean);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(zframe_val);
    char *string = String_val(string_val);
    bool cmp = zframe_streq(frame, string);
    boolean = Val_bool(cmp);

    CAMLreturn (boolean);
}

CAMLprim value
caml_zframe_more(value frame_val)
{
    CAMLparam1 (frame_val);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    int more = zframe_more(frame);
    
    CAMLreturn (Val_int(more));
}

CAMLprim value
caml_zframe_eq(value frame1_val, value frame2_val)
{
    CAMLparam2 (frame1_val, frame2_val);
    
    zframe_t *frame1 = CAML_CZMQ_zframe_val(frame1_val);
    zframe_t *frame2 = CAML_CZMQ_zframe_val(frame2_val);
    bool cmp = zframe_eq(frame1, frame2);
    
    CAMLreturn (Val_bool(cmp));
}

CAMLprim value
caml_zframe_print(value frame_val, value prefix_val)
{
    CAMLparam2 (frame_val, prefix_val);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    char *prefix = String_val(prefix_val); 
    zframe_print(frame, prefix);
    
    CAMLreturn (Val_unit);
}

CAMLprim value
caml_zframe_reset(value frame_val, value data_val, value size_val)
{
    CAMLparam3 (frame_val, data_val, size_val);
    
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    char *data = String_val(data_val);
    size_t size = Int_val(size_val); 
    zframe_reset(frame, data, size);
    
    CAMLreturn (Val_unit);
}

/******************
 *  zmsg          *
 ******************/

#define CAML_CZMQ_zmsg_val(v) (*(void **) Data_custom_val(v))

void caml_czmq_finalize_zmsg(value msg_val)
{
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zmsg_destroy (&msg);
}

static struct custom_operations caml_czmq_zmsg_ops = {
    identifier:     "org.czmq.zmsg",
    finalize:       caml_czmq_finalize_zmsg,
    compare:        custom_compare_default,
    hash:           custom_hash_default,
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};

static value caml_czmq_copy_zmsg(zmsg_t **zmsg) {
    CAMLparam0 ();
    CAMLlocal1 (msg_val);
    
    msg_val = caml_alloc_custom(&caml_czmq_zmsg_ops, sizeof(void *), 0, 1);
    memcpy( Data_custom_val(msg_val), zmsg, sizeof(void *) );   
    
    CAMLreturn (msg_val);
}

CAMLprim value
caml_zmsg_new()
{
    CAMLparam0 ();
    CAMLlocal1 (msg_val);
    
    zmsg_t *msg = zmsg_new();
    caml_zmq_raise_if(msg == NULL);
    msg_val = caml_czmq_copy_zmsg( &msg );
    
    CAMLreturn (msg_val);
}

CAMLprim value
caml_zmsg_recv(value socket_val)
{
    CAMLparam1 (socket_val);
    CAMLlocal1 (msg_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    zmsg_t *msg = zmsg_recv(socket_record->socket);
    if (! msg) caml_failwith("break");
    msg_val = caml_czmq_copy_zmsg(&msg);
    
    CAMLreturn (msg_val);
}

CAMLprim value
caml_zmsg_recv_nowait(value socket_val)
{
    CAMLparam1 (socket_val);
    CAMLlocal1 (msg_val);

    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    assert (socket_record->socket);
    zmsg_t *self = zmsg_new ();
    assert (self);

    bool received = true;
    while (1) {
        zframe_t *frame = zframe_recv_nowait(socket_record->socket);
        if (!frame) {
            zmsg_destroy(&self);
            received = false;
            break;              //  No message or incomplete message
        }
        if (zmsg_add(self, frame)) {
            zmsg_destroy(&self);
            break;
        }
        if (!zframe_more(frame))
            break;              //  Last message frame
    }

    if (received) {
        msg_val = caml_czmq_copy_zmsg(&self);
    } else {
        // if no msg received, return empty message
        zmsg_t *self = zmsg_new ();
        msg_val = caml_czmq_copy_zmsg(&self);
    }
    CAMLreturn (msg_val);
    
}


CAMLprim value
caml_zmsg_send(value msg_val, value socket_val)
{
    CAMLparam2 (msg_val, socket_val);
    
    socket_st *socket_record = CAML_CZMQ_zsocket_val(socket_val);
    // send a copy of msg, which is destroyed
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zmsg_t *msg_copy = zmsg_dup(msg);
    int rc = zmsg_send(&msg_copy, socket_record->socket);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zmsg_size(value msg_val)
{
    CAMLparam1 (msg_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    size_t size = zmsg_size(msg);
    
    CAMLreturn (Val_int((int) size));
}

CAMLprim value
caml_zmsg_content_size(value msg_val)
{
    CAMLparam1 (msg_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    size_t size = zmsg_content_size(msg);
    
    CAMLreturn (Val_int(size));
}

CAMLprim value
caml_zmsg_push(value msg_val, value frame_val)
{
    CAMLparam2 (msg_val, frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    // create a copy of frame and push that (copy to be destroyed by zmsg)
    zframe_t *framecpy = zframe_dup(frame);
    int rc = zmsg_push(msg, framecpy);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zmsg_pop(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_pop(msg);
    caml_zmq_raise_if(frame == NULL);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zmsg_add(value msg_val, value frame_val)
{
    CAMLparam2 (msg_val, frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    // create a copy of frame and add that (copy to be destroyed by zmsg)
    zframe_t *framecpy = zframe_dup(frame);
    int rc = zmsg_add(msg, framecpy);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zmsg_pushstr(value msg_val, value string_val)
{
    CAMLparam2 (msg_val, string_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    int size = caml_string_length(string_val);

    // push is done manually by constructing
    // a new frame to support binary strings

    // copy the bytes from the string
    unsigned char bytes[size];
    int i;
    for (i = 0; i < size; i++) 
    { 
        bytes[i] = Byte(string_val, i); 
    }

    void *frame = zframe_new(bytes, size);
    caml_zmq_raise_if(frame == NULL);
    int rc = zmsg_push(msg, frame);
    
    CAMLreturn (Val_int(rc));
}

// this duplicates zmsg_pushstr and can be deleted when no longer in use
CAMLprim value
caml_zmsg_pushbstr(value msg_val, value string_val, value size_val)
{
    CAMLparam3 (msg_val, string_val, size_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    int size = Int_val(size_val);
    
    // copy the bytes from the string
    unsigned char bytes[size];
    int i;
    for (i = 0; i < size; i++) 
    { 
        bytes[i] = Byte(string_val, i); 
    }

    // pass the bytes to the constructor of a 
    // new frame, which we will push 
    void *frame = zframe_new(bytes, size);
    caml_zmq_raise_if(frame == NULL);
    int rc = zmsg_push(msg, frame);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zmsg_addstr(value msg_val, value string_val)
{
    CAMLparam2 (msg_val, string_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    int size = caml_string_length(string_val);

    // push is done manually by constructing
    // a new frame to support binary strings

    // copy the bytes from the string
    unsigned char bytes[size];
    int i;
    for (i = 0; i < size; i++) 
    { 
        bytes[i] = Byte(string_val, i); 
    }

    void *frame = zframe_new(bytes, size);
    caml_zmq_raise_if(frame == NULL);
    int rc = zmsg_add(msg, frame);
    
    CAMLreturn (Val_int(rc));
}

CAMLprim value
caml_zmsg_popstr(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (bytes);
    
    // doing this manually to allow for binary strings
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_pop(msg);

    if (!frame) {
        // message is empty
        CAMLreturn (caml_copy_string(""));
    }

    size_t size = zframe_size(frame);
    char *dataptr = zframe_data(frame);

    // copy data to a new ocaml string
    bytes = caml_alloc_string(size);
    memcpy( String_val(bytes), dataptr, size);
    CAMLreturn( bytes );    
}

CAMLprim value
caml_zmsg_wrap(value msg_val, value frame_val)
{
    CAMLparam2 (msg_val, frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    // create a copy of frame and wrap that (copy to be destroyed by zmsg)
    zframe_t *framecpy = zframe_dup(frame);
    zmsg_wrap(msg, framecpy);
    
    CAMLreturn (Val_unit);
}

CAMLprim value
caml_zmsg_unwrap(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_unwrap(msg);
    caml_zmq_raise_if(frame == NULL);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zmsg_remove(value msg_val, value frame_val)
{
    CAMLparam2 (msg_val, frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zframe_t *frame = CAML_CZMQ_zframe_val(frame_val);
    zmsg_remove(msg, frame);
    
    CAMLreturn (Val_unit);
}

CAMLprim value
caml_zmsg_first(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_first(msg);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zmsg_next(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_next(msg);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zmsg_last(value msg_val)
{
    CAMLparam1 (msg_val);
    CAMLlocal1 (frame_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    void *frame = zmsg_last(msg);
    frame_val = caml_czmq_copy_zframe(&frame);
    
    CAMLreturn (frame_val);
}

CAMLprim value
caml_zmsg_dup(value orig_msg_val)
{
    CAMLparam1 (orig_msg_val);
    CAMLlocal1 (new_msg_val);

    zmsg_t *orig_msg = CAML_CZMQ_zmsg_val(orig_msg_val);
    zmsg_t *new_msg = zmsg_dup(orig_msg);
    caml_zmq_raise_if(new_msg == NULL);
    new_msg_val = caml_czmq_copy_zmsg(&new_msg);
    
    CAMLreturn (new_msg_val);
}

CAMLprim value
caml_zmsg_dump(value msg_val)
{
    CAMLparam1 (msg_val);
    
    zmsg_t *msg = CAML_CZMQ_zmsg_val(msg_val);
    zmsg_dump(msg);
    
    CAMLreturn (Val_unit);
}