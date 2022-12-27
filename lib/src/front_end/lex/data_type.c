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
    case DT_UNKNOWN: return "unknown";
    case DT_VOID:    return "void";
    case DT_INT:     return "int";
    case DT_FLOAT:   return "float";
    case DT_CHAR:    return "char";
    case DT_BOOL:    return "bool";
    case DT_STRUCT:  return "struct";
    default:         weak_unreachable("Should not reach there.");
    }
}