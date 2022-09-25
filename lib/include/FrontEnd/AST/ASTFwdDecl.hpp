/* ASTFwdDecl.hpp - AST forward declarations.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FWD_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_FWD_DECL_HPP

namespace weak {
namespace frontEnd {

class ASTNode;
class ASTArrayAccess;
class ASTArrayDecl;
class ASTBinaryOperator;
class ASTBooleanLiteral;
class ASTBreakStmt;
class ASTCompoundStmt;
class ASTContinueStmt;
class ASTDoWhileStmt;
class ASTFloatingPointLiteral;
class ASTForStmt;
class ASTFunctionCall;
class ASTFunctionDecl;
class ASTFunctionPrototype;
class ASTIfStmt;
class ASTIntegerLiteral;
class ASTReturnStmt;
class ASTStringLiteral;
class ASTSymbol;
class ASTUnaryOperator;
class ASTVarDecl;
class ASTWhileStmt;

} // namespace frontEnd
} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FWD_DECL_HPP