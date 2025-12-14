import ./core
import ./core_macros



proc leftMost*(node: Node): Node =
  if node.len == 0:
    return node
  elif node.kind == nkInfix:
    return leftMost(node[1])  # For infix, go to left operand
  else:
    return leftMost(node[0])

proc leftMost*(node: seq[Node]): Node =
  return leftMost(node[0])

proc rightMost*(node: Node): Node =
  if node.len == 0:
    return node
  elif node.kind == nkInfix:
    expectLen(node, 3)
    return rightMost(node[2])  # For infix, go to right operand
  else:
    expectMinLen(node, 1)
    return rightMost(node[node.len - 1])  # Go to last child

proc whenKind*(n: Node, k: NodeKind): bool =
  return n.kind == k

proc cmdName*(n: Node): string =
  if n.kind notin {nkCall, nkCommand}:
    error("Expected a call or command node", n)
  else:
    expectMinLen(n, 1)
    result = n[0].rightMost.strVal

proc whenCmd*(node: Node, name: string): bool =
  # echo "When CMD!"
  # echo node.treeRepr
  return node.kind == nkCommand and node.cmdName == name

proc whenCmd*(node: Node, names: varargs[string]): bool =
  return node.kind == nkCommand and node.cmdName in names

proc whenCmdName*(node: Node, name: varargs[string]): bool =
  # return node.cmdName == name
  return node.cmdName in name



proc getEndModule*(node: Node): Node =
  var currentNode = node
  if currentNode.kind == nkStmtList:
    currentNode = currentNode[0]
  
  if currentNode.kind == nkIdent:
    return currentNode
  elif currentNode.kind == nkInfix:
    return currentNode.rightMost()
  else:
    error "Expected an identifier or infix expression", currentNode


proc expectArgLen*(node: Node, argLen: int) =
  var lastNode = node[node.len - 1] or node

  if node.len != argLen + 1:
    # error "Invalid " & nm & ", expected " & $argLen & " arguments, but got " & $(node.len - 1), lastNode
    # echo "Invalid " & nm & ", expected " & $argLen & " arguments, but got " & $(node.len - 1)
    echo "Expected " & $argLen & " arguments, but got " & $(node.len - 1) & " in " & node.repr
    quit(1)

proc expectArgLen*(node: Node, argLens: seq[int]) =  
  var lastNode = node[node.len - 1] or node

  if not node.len - 1 in argLens:
    # error "Invalid " & nm & ", expected " & argLens.repr & " arguments, but got " & $(node.len - 1), lastNode
    # echo "Invalid " & nm & ", expected " & argLens.repr & " arguments, but got " & $(node.len - 1)
    echo "Expected one of " & argLens.repr & " arguments, but got " & $(node.len - 1) & " in " & node.repr
    quit(1)


proc isField*(node: Node): bool =
  return node.whenKind(nkCall) and node.len == 2 and (node[0].whenKind(nkIdent) or node[0].whenKind(nkPragmaExpr)) and node[1].whenKind(nkStmtList)

proc isEnumAssgn*(node: Node): bool =
  return node.whenKind(nkAsgn) and node[0].kind == nkIdent and node[0].strVal != "result" and node[1].kind in {nkStrLit, nkIntLit, nkFloatLit, nkCharLit, nkNilLit}

proc isIdent*(node: Node): bool =
  return node.kind == nkIdent

proc isUntypedVarargs*(node: Node): bool =
  node.kind == nkBracketExpr and node.len == 2 and node[0].whenKind(nkIdent) and node[0].strVal == "varargs" and node[1].whenKind(nkIdent) and node[1].strVal == "untyped"

# if Node is empty if someone does `node == nil`
proc isEmpty*(node: Node): bool =
  return node.kind == NodeKind.nkEmpty