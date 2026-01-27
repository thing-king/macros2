# Compile-time logging (no pkg/debug import to avoid circular deps)
proc ctLog(msg: string) =
  echo "[CONV] " & msg

proc toNode*(n: NimNode): Node =
  ## Convert a NimNode to a macros2.Node
  try:
    let nk = n.kind.toNodeKind()

    result = Node(
      kind: nk,
      repr: "",
      info: NodeLineInfo(
        filename: n.lineInfoObj.filename,
        line: n.lineInfoObj.line,
        column: n.lineInfoObj.column
      )
    )

    case nk
    of STR_LITERALS:
      if n.kind in {nnkStrLit..nnkTripleStrLit, nnkCommentStmt, nnkIdent, nnkSym}:
        result.strVal = n.strVal
        result.repr = n.strVal
      else:
        ctLog "ERROR: STR_LITERALS but NimNode " & $n.kind & " has no strVal"
        raise newException(FieldDefect, "toNode: NimNode kind " & $n.kind & " has no strVal")
    of INT_LITERALS:
      result.intVal = n.intVal
      result.repr = $n.intVal
    of FLOAT_LITERALS:
      result.floatVal = n.floatVal
      result.repr = $n.floatVal
    of CAN_HAVE_CHILDREN:
      result.children = newSeq[Node](n.len)
      for i in 0..<n.len:
        result.children[i] = n[i].toNode()
      try:
        result.repr = n.repr
      except:
        result.repr = "<repr failed>"
    of nkEmpty, nkNilLit:
      result.repr = if nk == nkNilLit: "nil" else: ""
  except FieldDefect as e:
    ctLog "FIELD DEFECT: " & e.msg
    raise
  except Exception as e:
    ctLog "EXCEPTION: " & e.msg
    raise

proc toNimNode*(n: Node): NimNode =
  ## Convert a macros2.Node back to NimNode
  try:
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
        if n.strVal == "_":
          let stmt = macros.parseStmt("discard _")
          result = stmt[0][0].copyNimTree()
        else:
          result = macros.ident(n.strVal)
      of nkSym:
        result = macros.ident(n.strVal)
      else:
        result = macros.newNimNode(n.kind.toNimNodeKind())
        result.strVal = n.strVal
    of INT_LITERALS:
      result = macros.newNimNode(n.kind.toNimNodeKind())
      result.intVal = n.intVal
    of FLOAT_LITERALS:
      result = macros.newLit(n.floatVal)
    of CAN_HAVE_CHILDREN:
      result = macros.newNimNode(n.kind.toNimNodeKind())
      for child in n.children:
        result.add(child.toNimNode())
    of nkEmpty:
      result = macros.newEmptyNode()
    of nkNilLit:
      result = macros.newNilLit()
  except Exception as e:
    ctLog "ERROR toNimNode " & $n.kind & ": " & e.msg
    raise