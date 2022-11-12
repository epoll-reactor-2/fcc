/* DataType.h - Definition of data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H
#define WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H

namespace weak {

enum DataType {
  DT_UNKNOWN,
  DT_FUNC,
  DT_STRUCT,
  DT_VOID,
  DT_INT,
  DT_CHAR,
  DT_STRING,
  DT_FLOAT,
  DT_BOOL
};

const char *DataTypeToString(DataType);

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_LEX_DATA_TYPE_H