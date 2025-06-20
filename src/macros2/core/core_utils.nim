import system except NimNode
import ./core
import ./core_macros

proc copyNimTree*(node: NimNode): NimNode =
  ## Creates a deep copy of `node` and all its children
  
  let kind = node.kind
  result = newNimNode(kind)
  result.intVal = node.intVal
  result.floatVal = node.floatVal
  result.strVal = node.strVal
  result.ident = node.ident
  result.sym = node.sym
  for child in node.children:
    result.add child.copyNimTree()


proc copy*(node: NimNode): NimNode =
  ## An alias for `copyNimTree<#copyNimTree,NimNode>`_.
  return node.copyNimTree()



proc leftMost*(node: NimNode): NimNode =
  if node.len == 0:
    return node
  elif node.kind == nnkInfix:
    return leftMost(node[1])  # For infix, go to left operand
  else:
    return leftMost(node[0])

proc leftMost*(node: seq[NimNode]): NimNode =
  return leftMost(node[0])

proc rightMost*(node: NimNode): NimNode =
  if node.len == 0:
    return node
  elif node.kind == nnkInfix:
    return rightMost(node[2])  # For infix, go to right operand
  else:
    return rightMost(node[node.len - 1])  # Go to last child

proc whenKind*(n: NimNode, k: NimNodeKind): bool =
  return n.kind == k

proc cmdName*(n: NimNode): string =
  if n.kind notin {nnkCall, nnkCommand}:
    error("Expected a call or command node", n)
  result = n[0].rightMost.strVal

proc whenCmd*(node: NimNode, name: string): bool =
  # echo "When CMD!"
  # echo node.treeRepr
  return node.kind == nnkCommand and node.cmdName == name

proc whenCmd*(node: NimNode, names: varargs[string]): bool =
  return node.kind == nnkCommand and node.cmdName in names

proc whenCmdName*(node: NimNode, name: varargs[string]): bool =
  # return node.cmdName == name
  return node.cmdName in name



proc getEndModule*(node: NimNode): NimNode =
  var currentNode = node
  if currentNode.kind == nnkStmtList:
    currentNode = currentNode[0]
  
  if currentNode.kind == nnkIdent:
    return currentNode
  elif currentNode.kind == nnkInfix:
    return currentNode.rightMost()
  else:
    error "Expected an identifier or infix expression", currentNode


proc expectArgLen*(node: NimNode, argLen: int) =
  var lastNode = node[node.len - 1] or node
  var nm = name(node)

  if node.len != argLen + 1:
    # error "Invalid " & nm & ", expected " & $argLen & " arguments, but got " & $(node.len - 1), lastNode
    # echo "Invalid " & nm & ", expected " & $argLen & " arguments, but got " & $(node.len - 1)
    echo "Expected " & $argLen & " arguments, but got " & $(node.len - 1) & " in " & nm.repr
    quit(1)

proc expectArgLen*(node: NimNode, argLens: seq[int]) =  
  var lastNode = node[node.len - 1] or node
  var nm = name(node)

  if not node.len - 1 in argLens:
    # error "Invalid " & nm & ", expected " & argLens.repr & " arguments, but got " & $(node.len - 1), lastNode
    # echo "Invalid " & nm & ", expected " & argLens.repr & " arguments, but got " & $(node.len - 1)
    echo "Expected one of " & argLens.repr & " arguments, but got " & $(node.len - 1) & " in " & nm.repr
    quit(1)


proc isField*(node: NimNode): bool =
  return node.whenKind(nnkCall) and node.len == 2 and (node[0].whenKind(nnkIdent) or node[0].whenKind(nnkPragmaExpr)) and node[1].whenKind(nnkStmtList)

proc isEnumAssgn*(node: NimNode): bool =
  return node.whenKind(nnkAsgn) and node[0].kind == nnkIdent and node[0].strVal != "result" and node[1].kind in {nnkStrLit, nnkIntLit, nnkFloatLit, nnkCharLit, nnkNilLit}

proc isIdent*(node: NimNode): bool =
  return node.kind == nnkIdent

proc isUntypedVarargs*(node: NimNode): bool =
  # node.kind == "nnkBracketExpr" and node.children.len == 2 and node.children[0].strVal == "varargs" and node.children[1].strVal == "untyped"
  node.kind == nnkBracketExpr and node.len == 2 and node[0].whenKind(nnkIdent) and node[0].strVal == "varargs" and node[1].whenKind(nnkIdent) and node[1].strVal == "untyped"
