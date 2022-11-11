/* DataType.cpp - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Lex/DataType.h"
#include "Utility/Diagnostic.h"

std::string weak::DataTypeToString(DataType T) {
  switch (T) {
  case DT_VOID:
    return "<VOID>";
  case DT_INT:
    return "<INT>";
  case DT_FLOAT:
    return "<FLOAT>";
  case DT_CHAR:
    return "<CHAR>";
  case DT_STRING:
    return "<STRING>";
  case DT_BOOL:
    return "<BOOLEAN>";
  case DT_STRUCT:
    return "<STRUCT>";
  default:
    Unreachable();
  }
}