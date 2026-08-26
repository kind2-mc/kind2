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
static HANDLE kind2_timeout_job = NULL;

/* Say what is happening, from a thread of its own.

   A write to the standard error of Kind 2 blocks rather than failing
   when it is a pipe whose reader has stopped, and this is the path that
   must not be stoppable. The OCaml last resort bounds its own writes
   for the same reason. */
static DWORD WINAPI kind2_timeout_announce(LPVOID unused)
{
  (void)unused;
  fprintf(stderr,
          "Kind 2 ran past its timeout without stopping, terminating.\n");
  fflush(stderr);
  return 0;
}

static DWORD WINAPI kind2_timeout_thread(LPVOID unused)
{
  HANDLE announce;
  (void)unused;
  Sleep(kind2_timeout_ms);

  /* Nothing below enters the runtime, so a rendezvous holding every
     domain does not hold this. */
  announce = CreateThread(NULL, 0, kind2_timeout_announce, NULL, 0, NULL);
  if (announce != NULL) {
    /* Above the rest, and given several seconds. This fires on a
       machine whose every core is held by domains spinning at a
       rendezvous, and a thread of ordinary priority given a second did
       not get to run at all: the process was ended on time and said
       nothing about why, which is the one thing it is here to do.
       Bounded still, since a standard error nobody drains must not be
       what keeps us from exiting. */
    SetThreadPriority(announce, THREAD_PRIORITY_HIGHEST);
    WaitForSingleObject(announce, 5000);
    CloseHandle(announce);
  }

  /* The job first, when there is one: it holds this process and the
     solvers it started, and ends them together. Ending only this
     process would leave a solver that is inside a query -- one that is
     idle reads the end of its standard input and goes, but one that is
     working does not read it until the query returns, and that is not
     bounded. Every other exit path kills the solvers for that reason.

     `TerminateJobObject` does not return, so the fallback below runs
     only if there is no job to end. */
  if (kind2_timeout_job != NULL)
    TerminateJobObject(kind2_timeout_job, kind2_timeout_status);
  TerminateProcess(GetCurrentProcess(), kind2_timeout_status);
  return 0;
}

CAMLprim value kind2_arm_native_timeout(value seconds, value status)
{
  CAMLparam2(seconds, status);
  HANDLE thread;
  kind2_timeout_ms = (DWORD) (Long_val(seconds) * 1000);
  kind2_timeout_status = (UINT) Long_val(status);

  /* A job this process and its children belong to, so that the thread
     can end them together. A child joins the job of its parent unless
     it asks not to, and the solvers do not ask. Nesting has been
     allowed since Windows 8, so being in a job already -- which a CI
     runner arranges -- is not a reason this fails.

     The handle stays open for the life of the process, and the job is
     deliberately not created with JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE:
     closing it must not be what ends the run. */
  kind2_timeout_job = CreateJobObject(NULL, NULL);
  if (kind2_timeout_job != NULL
      && !AssignProcessToJobObject(kind2_timeout_job, GetCurrentProcess())) {
    CloseHandle(kind2_timeout_job);
    kind2_timeout_job = NULL;   /* fall back to ending this process alone */
  }

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
