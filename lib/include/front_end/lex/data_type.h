/* data_type.h - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H
#define WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H

typedef enum {
    DT_UNKNOWN,
    DT_FUNC,
    DT_STRUCT,
    DT_VOID,
    DT_INT,
    DT_CHAR,
    DT_STRING,
    DT_FLOAT,
    DT_BOOL
} data_type_e;

/// \return String representation of the token. Don't
///         apply free() to the result.
///
/// \note   weak_unreachable() called on unknown integer value of dt.
const char *data_type_to_string(data_type_e dt);

#endif // WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H