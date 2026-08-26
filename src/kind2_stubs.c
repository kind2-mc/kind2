/* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License.

*/

/* A wall clock for Windows that the runtime cannot stop.

   Kind 2 checks its own wall clock in the polling loop of the
   supervisor, which is enough while the supervisor runs. On Windows
   with more engines busy than the machine has cores it stops running:
   the domains cannot all reach a stop-the-world rendezvous, so every
   one of them parks in it, and no OCaml code executes anywhere in the
   process for seconds at a stretch. A thread of the supervisor's domain
   and a domain of its own were both measured stopped throughout. So no
   timeout written in OCaml can fire, and the process runs minutes past
   the timeout it was given.

   The process itself is not stopped -- it holds every core while this
   happens, spinning in the runtime. What is stopped is OCaml. A thread
   the operating system made, which never takes the master lock and
   calls nothing in the runtime, is scheduled as usual and can end the
   process on time.

   POSIX needs none of this: `setitimer` delivers SIGALRM, and the
   handler runs at the next poll point. */

#include <caml/mlvalues.h>
#include <caml/memory.h>

#ifdef _WIN32

#include <windows.h>
#include <stdio.h>

static DWORD kind2_timeout_ms = 0;
static UINT kind2_timeout_status = 0;

static DWORD WINAPI kind2_timeout_thread(LPVOID unused)
{
  (void)unused;
  Sleep(kind2_timeout_ms);
  /* Nothing below enters the runtime, so a rendezvous holding every
     domain does not hold this. */
  fprintf(stderr,
          "Kind 2 ran past its timeout without stopping, terminating.\n");
  fflush(stderr);
  TerminateProcess(GetCurrentProcess(), kind2_timeout_status);
  return 0;
}

CAMLprim value kind2_arm_native_timeout(value seconds, value status)
{
  CAMLparam2(seconds, status);
  HANDLE thread;
  kind2_timeout_ms = (DWORD) (Long_val(seconds) * 1000);
  kind2_timeout_status = (UINT) Long_val(status);
  thread = CreateThread(NULL, 0, kind2_timeout_thread, NULL, 0, NULL);
  if (thread != NULL) CloseHandle(thread);
  CAMLreturn(Val_unit);
}

#else

CAMLprim value kind2_arm_native_timeout(value seconds, value status)
{
  CAMLparam2(seconds, status);
  CAMLreturn(Val_unit);
}

#endif
