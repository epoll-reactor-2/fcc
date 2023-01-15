/* data_type.c - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/data_type.h"
#include "utility/unreachable.h"

const char *data_type_to_string(data_type_e dt)
{
    switch (dt) {
    case D_T_UNKNOWN: return "unknown";
    case D_T_VOID:    return "void";
    case D_T_INT:     return "int";
    case D_T_FLOAT:   return "float";
    case D_T_CHAR:    return "char";
    case D_T_BOOL:    return "boolean";
    case D_T_STRING:  return "string";
    case D_T_STRUCT:  return "struct";
    default:         weak_unreachable("Should not reach there.");
    }
}