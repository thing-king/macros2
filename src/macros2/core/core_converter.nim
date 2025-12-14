proc toNode*(n: NimNode): Node =
  let nk = n.kind.toNodeKind()
  let lineInfo = n.lineInfoObj
  
  result = Node(
    kind: nk,
    repr: n.repr,
    info: NodeLineInfo(
      filename: lineInfo.filename,
      line: lineInfo.line,
      column: lineInfo.column
    )
  )
  
  case nk
  of STR_LITERALS:
    result.strVal = n.strVal
  of INT_LITERALS:
    result.intVal = n.intVal
  of FLOAT_LITERALS:
    result.floatVal = n.floatVal
  of CAN_HAVE_CHILDREN:
    result.children = newSeq[Node](n.len)
    for i in 0..<n.len:
      result.children[i] = n[i].toNode()
  of nkEmpty, nkNilLit:
    discard

proc toNimNode*(n: Node): NimNode =
  try:
    # Handle nkNone as empty node
    if n.kind == nkNone:
      return macros.newEmptyNode()
    
    case n.kind
    of STR_LITERALS:
      case n.kind
      of nkStrLit:
        result = macros.newLit(n.strVal)
      of nkRStrLit:
        result = macros.newNimNode(nnkRStrLit)
        result.strVal = n.strVal
      of nkTripleStrLit:
        result = macros.newNimNode(nnkTripleStrLit)
        result.strVal = n.strVal
      of nkCommentStmt:
        result = macros.newCommentStmtNode(n.strVal)
      of nkIdent:
        result = macros.ident(n.strVal)
      of nkSym:
        result = macros.ident(n.strVal)
      else:
        result = macros.newNimNode(n.kind.toNimNodeKind())
        result.strVal = n.strVal
    of INT_LITERALS:
      result = macros.newLit(n.intVal)
    of FLOAT_LITERALS:
      result = macros.newLit(n.floatVal)
    of CAN_HAVE_CHILDREN:
      result = macros.newNimNode(n.kind.toNimNodeKind())
      for i, child in n.children:
        let converted = child.toNimNode()
        result.add(converted)
    of nkEmpty:
      result = macros.newEmptyNode()
    of nkNilLit:
      result = macros.newNilLit()
  except Exception as e:
    echo "ERROR converting node kind ", n.kind, ": ", e.msg
    echo "Node tree:"
    # echo n.treeRepr
    raise