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

#include "testutil.hpp"

int main (void)
{
    setup_test_environment();
    void *ctx = zmq_ctx_new ();
    assert (ctx);

    void *sock = zmq_socket (ctx, ZMQ_PUB);
    assert (sock);

    int rc = zmq_connect (sock, "tcp://localhost:1234");
    assert (rc == 0);

    rc = zmq_connect (sock, "tcp://[::1]:1234");
    assert (rc == 0);

    rc = zmq_connect (sock, "tcp://localhost:invalid");
    assert (rc == -1);

    rc = zmq_connect (sock, "tcp://in val id:1234");
    assert (rc == -1);
    
    rc = zmq_connect (sock, "tcp://");
    assert (rc == -1);
    
    rc = zmq_connect (sock, "tcp://192.168.0.200:*");
    assert (rc == -1);

    rc = zmq_connect (sock, "invalid://localhost:1234");
    assert (rc == -1);
    assert (errno == EPROTONOSUPPORT);

    rc = zmq_close (sock);
    assert (rc == 0);

    rc = zmq_ctx_term (ctx);
    assert (rc == 0);

    return 0;
}
