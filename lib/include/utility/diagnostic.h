/* diagnostic.h - Diagnostics engine.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_DIAGNOSTICS_H
#define WEAK_COMPILER_UTILITY_DIAGNOSTICS_H

#include <stdint.h>
#include <setjmp.h>
#include <stdnoreturn.h>

/// Jump buffer for handling errors. As warning/errors emit
/// functions, can be used in normal "real-world" compiler mode
/// as well as in testing mode.
///
/// \note Driver code should do similar thing
///
/// \code{.c}
/// if (!setjmp(fatal_error_buf)) {
///     /// Normal code.
/// } else {
///     /// Fallback on error inside normal code.
/// }
/// \endcode
extern jmp_buf weak_fatal_error_buf;

/// Streams being FILE *, used for debug purposes. There are
/// two cases:
/// - streams are NULL, then all compiler outputs written to the screen and program
///   terminates on compile error;
/// - streams are set, then all compiler outputs written to it.
///
/// void *diag_error_memstream;
/// void *diag_warn_memstream;

/// Emit compile error and go out from executor function of any depth to defined
/// (as written above) error handler code.
noreturn
void weak_compile_error(uint16_t line_no, uint16_t col_no, const char *fmt, ...);
void weak_compile_warn (uint16_t line_no, uint16_t col_no, const char *fmt, ...);

#endif // WEAK_COMPILER_UTILITY_DIAGNOSTICS_H