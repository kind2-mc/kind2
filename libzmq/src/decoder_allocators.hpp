/*
    Copyright (c) 2007-2015 Contributors as noted in the AUTHORS file

    This file is part of libzmq, the ZeroMQ core engine in C++.

    libzmq is free software; you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.

    As a special exception, the Contributors give you permission to link
    this library with independent modules to produce an executable,
    regardless of the license terms of these independent modules, and to
    copy and distribute the resulting executable under terms of your choice,
    provided that you also meet, for each linked independent module, the
    terms and conditions of the license of that module. An independent
    module is a module which is not derived from or based on this library.
    If you modify this library, you must extend this exception to your
    version of the library.

    libzmq is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
    License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef __ZMQ_DECODER_ALLOCATORS_HPP_INCLUDED__
#define __ZMQ_DECODER_ALLOCATORS_HPP_INCLUDED__

#include <cstddef>
#include <cstdlib>

#include "atomic_counter.hpp"
#include "err.hpp"

namespace zmq
{
    // Static buffer policy.
    class c_single_allocator
    {
    public:
        explicit c_single_allocator (std::size_t bufsize_) :
                bufsize(bufsize_),
                buf(static_cast <unsigned char*> (std::malloc (bufsize)))
        {
            alloc_assert (buf);
        }

        ~c_single_allocator ()
        {
            std::free (buf);
        }

        unsigned char* allocate ()
        {
            return buf;
        }

        void deallocate ()
        {
        }

        std::size_t size () const
        {
            return bufsize;
        }

        void resize (std::size_t new_size)
        {
            bufsize = new_size;
        }
    private:
        std::size_t bufsize;
        unsigned char* buf;

        c_single_allocator (c_single_allocator const&);
        c_single_allocator& operator = (c_single_allocator const&);
    };

    // This allocator allocates a reference counted buffer which is used by v2_decoder_t
    // to use zero-copy msg::init_data to create messages with memory from this buffer as
    // data storage.
    //
    // The buffer is allocated with a reference count of 1 to make sure that is is alive while
    // decoding messages. Otherwise, it is possible that e.g. the first message increases the count
    // from zero to one, gets passed to the user application, processed in the user thread and deleted
    // which would then deallocate the buffer. The drawback is that the buffer may be allocated longer
    // than necessary because it is only deleted when allocate is called the next time.
    class shared_message_memory_allocator
    {
    public:
        explicit shared_message_memory_allocator (std::size_t bufsize_);

        // Create an allocator for a maximum number of messages
        shared_message_memory_allocator (std::size_t bufsize_, std::size_t maxMessages);

        ~shared_message_memory_allocator ();

        // Allocate a new buffer
        //
        // This releases the current buffer to be bound to the lifetime of the messages
        // created on this buffer.
        unsigned char* allocate ();

        // force deallocation of buffer.
        void deallocate ();

        // Give up ownership of the buffer. The buffer's lifetime is now coupled to
        // the messages constructed on top of it.
        unsigned char* release ();

        void inc_ref ();

        static void call_dec_ref (void*, void* buffer);

        std::size_t size () const;

        // Return pointer to the first message data byte.
        unsigned char* data ();

        // Return pointer to the first byte of the buffer.
        unsigned char* buffer ()
        {
            return buf;
        }

        void resize (std::size_t new_size)
        {
            bufsize = new_size;
        }

        zmq::atomic_counter_t* provide_refcnt ()
        {
            return msg_refcnt;
        }

        void advance_refcnt ()
        {
            msg_refcnt++;
        }

    private:
        unsigned char* buf;
        std::size_t bufsize;
        std::size_t max_size;
        zmq::atomic_counter_t* msg_refcnt;
        std::size_t maxCounters;
    };
}

#endif
