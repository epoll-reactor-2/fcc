/* DataType.cpp - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Lex/DataType.h"
#include "Utility/Unreachable.h"

const char *weak::DataTypeToString(DataType T) {
  switch (T) {
  case DT_UNKNOWN: return "unknown";
  case DT_FUNC:    return "function";
  case DT_VOID:    return "void";
  case DT_INT:     return "int";
  case DT_FLOAT:   return "float";
  case DT_CHAR:    return "char";
  case DT_STRING:  return "string";
  case DT_BOOL:    return "bool";
  case DT_STRUCT:  return "struct";
  default:         Unreachable("Should not reach there.");
  }
}