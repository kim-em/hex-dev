/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
*/
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>
#ifndef _WIN32
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <unistd.h>
#endif

static lean_obj_res pipe_error(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/* Lean v4.35 erases the IO world argument. Its FS.Handle owns a FILE*. These
   fresh pipe handles have not been read through stdio, so their descriptors
   have no buffered input to lose. Only the dedicated reader accesses each. */
LEAN_EXPORT lean_obj_res hex_ecpp_poll_read(b_lean_obj_arg handle) {
#ifdef _WIN32
    (void)handle;
    return pipe_error("PARI: interruptible pipes require POSIX");
#else
    FILE *stream = (FILE *)lean_get_external_data(handle);
    int fd = fileno(stream);
    int flags = fcntl(fd, F_GETFL);
    if (flags == -1 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) == -1)
        return pipe_error(strerror(errno));
    struct pollfd descriptor = {fd, POLLIN, 0};
    int ready = poll(&descriptor, 1, 25);
    if (ready == 0 || (ready == -1 && errno == EINTR))
        return lean_io_result_mk_ok(lean_box(0));
    if (ready == -1) return pipe_error(strerror(errno));
    lean_object *bytes = lean_alloc_sarray(1, 0, 4096);
    ssize_t count = read(fd, lean_sarray_cptr(bytes), 4096);
    if (count < 0) {
        int saved_errno = errno;
        lean_dec(bytes);
        if (saved_errno == EAGAIN || saved_errno == EWOULDBLOCK || saved_errno == EINTR)
            return lean_io_result_mk_ok(lean_box(0));
        return pipe_error(strerror(saved_errno));
    }
    lean_sarray_set_size(bytes, (size_t)count);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, bytes);
    return lean_io_result_mk_ok(some);
#endif
}

LEAN_EXPORT lean_obj_res hex_ecpp_kill_group(uint32_t pid) {
#ifdef _WIN32
    (void)pid;
    return pipe_error("PARI: process-group cleanup requires POSIX");
#else
    if (pid == 0 || pid > INT_MAX) return pipe_error("PARI: invalid child PID");
    if (kill(-(pid_t)pid, SIGKILL) == -1) {
        if (errno != ESRCH) return pipe_error(strerror(errno));
        /* spawn may return before the child's setsid has created its group.
           The leader is still owned and unreaped, preventing PID reuse. */
        if (kill((pid_t)pid, SIGKILL) == -1 && errno != ESRCH)
            return pipe_error(strerror(errno));
        /* setsid and fork may race the fallback. The unreaped leader still
           reserves this group ID, so a second group kill cannot hit reuse. */
        if (kill(-(pid_t)pid, SIGKILL) == -1 && errno != ESRCH)
            return pipe_error(strerror(errno));
    }
    return lean_io_result_mk_ok(lean_box(0));
#endif
}
