/* data_type.h - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H
#define WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H

typedef enum {
    D_T_UNKNOWN,
    D_T_FUNC,
    D_T_STRUCT,
    D_T_VOID,
    D_T_INT,
    D_T_CHAR,
    D_T_STRING,
    D_T_FLOAT,
    D_T_BOOL
} data_type_e;

/// \return String representation of the token. Don't
///         apply free() to the result.
///
/// \note   weak_unreachable() called on unknown integer value of dt.
const char *data_type_to_string(data_type_e dt);

#endif // WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H