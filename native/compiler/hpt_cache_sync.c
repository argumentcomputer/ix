#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

static lean_obj_res compilatrix_sync_error(int error, b_lean_obj_arg path) {
    return lean_io_result_mk_error(lean_decode_io_error(error, path));
}

static int compilatrix_open_retry(char const *path, int flags) {
    int descriptor;
    do {
        descriptor = open(path, flags);
    } while (descriptor < 0 && errno == EINTR);
    return descriptor;
}

static int compilatrix_fsync_retry(int descriptor) {
    int result;
    do {
        result = fsync(descriptor);
    } while (result < 0 && errno == EINTR);
    return result;
}

static int compilatrix_sync_regular_file(int descriptor) {
#if defined(__APPLE__) && defined(F_FULLFSYNC)
    int result;
    do {
        result = fcntl(descriptor, F_FULLFSYNC, 0);
    } while (result < 0 && errno == EINTR);
    if (result == 0) {
        return 0;
    }
    if (errno != EINVAL && errno != ENOTSUP) {
        return result;
    }
#endif
    return compilatrix_fsync_retry(descriptor);
}

static lean_obj_res compilatrix_sync_path(
    b_lean_obj_arg path,
    int expected_directory
) {
    int flags = expected_directory ? O_RDONLY : O_RDWR;
#ifdef O_CLOEXEC
    flags |= O_CLOEXEC;
#endif
#ifdef O_NOFOLLOW
    flags |= O_NOFOLLOW;
#endif
#ifdef O_DIRECTORY
    if (expected_directory) {
        flags |= O_DIRECTORY;
    }
#endif

    int descriptor = compilatrix_open_retry(lean_string_cstr(path), flags);
    if (descriptor < 0) {
        return compilatrix_sync_error(errno, path);
    }

    struct stat metadata;
    if (fstat(descriptor, &metadata) < 0) {
        int error = errno;
        (void)close(descriptor);
        return compilatrix_sync_error(error, path);
    }
    if (expected_directory ? !S_ISDIR(metadata.st_mode) : !S_ISREG(metadata.st_mode)) {
        int error = expected_directory ? ENOTDIR : EISDIR;
        (void)close(descriptor);
        return compilatrix_sync_error(error, path);
    }

    int result = expected_directory
        ? compilatrix_fsync_retry(descriptor)
        : compilatrix_sync_regular_file(descriptor);
    int error = result < 0 ? errno : 0;
    if (close(descriptor) < 0 && error == 0) {
        error = errno;
    }
    if (error != 0) {
        return compilatrix_sync_error(error, path);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res compilatrix_durable_sync_file(
    b_lean_obj_arg path,
    lean_obj_arg world
) {
    (void)world;
    return compilatrix_sync_path(path, 0);
}

LEAN_EXPORT lean_obj_res compilatrix_durable_sync_directory(
    b_lean_obj_arg path,
    lean_obj_arg world
) {
    (void)world;
    return compilatrix_sync_path(path, 1);
}
