/* data_type.h - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H
#define WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H

#include "util/compiler.h"

enum data_type {
    D_T_UNKNOWN = 0,
    D_T_FUNC,
    D_T_STRUCT,
    D_T_VOID,
    D_T_INT,
    D_T_CHAR,
    D_T_STRING,
    D_T_FLOAT,
    D_T_BOOL,
    D_T_TOTAL
};

extern int data_type_size[D_T_TOTAL];

/** \return String representation of the token. Don't
            apply free() to the result.
   
    \note   weak_unreachable() called on unknown integer value of dt. */
wur const char *data_type_to_string(enum data_type dt);

#endif // WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H