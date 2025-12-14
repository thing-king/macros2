import macros except newStmtList, newIdent, newCall, ident, newLit,
  newIntLit, newFloatLit, newStrLit

import pkg/jsony

type
  NodeKind* = enum
    nkNone, nkEmpty, nkIdent, nkSym,
    nkType, nkCharLit, nkIntLit, nkInt8Lit,
    nkInt16Lit, nkInt32Lit, nkInt64Lit, nkUIntLit, nkUInt8Lit,
    nkUInt16Lit, nkUInt32Lit, nkUInt64Lit, nkFloatLit,
    nkFloat32Lit, nkFloat64Lit, nkFloat128Lit, nkStrLit, nkRStrLit,
    nkTripleStrLit, nkNilLit, nkComesFrom, nkDotCall,
    nkCommand, nkCall, nkCallStrLit, nkInfix,
    nkPrefix, nkPostfix, nkHiddenCallConv,
    nkExprEqExpr,
    nkExprColonExpr, nkIdentDefs, nkVarTuple,
    nkPar, nkObjConstr, nkCurly, nkCurlyExpr,
    nkBracket, nkBracketExpr, nkPragmaExpr, nkRange,
    nkDotExpr, nkCheckedFieldExpr, nkDerefExpr, nkIfExpr,
    nkElifExpr, nkElseExpr, nkLambda, nkDo, nkAccQuoted,
    nkTableConstr, nkBind,
    nkClosedSymChoice,
    nkOpenSymChoice,
    nkHiddenStdConv,
    nkHiddenSubConv, nkConv, nkCast, nkStaticExpr,
    nkAddr, nkHiddenAddr, nkHiddenDeref, nkObjDownConv,
    nkObjUpConv, nkChckRangeF, nkChckRange64, nkChckRange,
    nkStringToCString, nkCStringToString, nkAsgn,
    nkFastAsgn, nkGenericParams, nkFormalParams, nkOfInherit,
    nkImportAs, nkProcDef, nkMethodDef, nkConverterDef,
    nkMacroDef, nkTemplateDef, nkIteratorDef, nkOfBranch,
    nkElifBranch, nkExceptBranch, nkElse,
    nkAsmStmt, nkPragma, nkPragmaBlock, nkIfStmt, nkWhenStmt,
    nkForStmt, nkParForStmt, nkWhileStmt, nkCaseStmt,
    nkTypeSection, nkVarSection, nkLetSection, nkConstSection,
    nkConstDef, nkTypeDef,
    nkYieldStmt, nkDefer, nkTryStmt, nkFinally, nkRaiseStmt,
    nkReturnStmt, nkBreakStmt, nkContinueStmt, nkBlockStmt, nkStaticStmt,
    nkDiscardStmt, nkStmtList,
    nkImportStmt,
    nkImportExceptStmt,
    nkExportStmt,
    nkExportExceptStmt,
    nkFromStmt,
    nkIncludeStmt,
    nkBindStmt, nkMixinStmt, nkUsingStmt,
    nkCommentStmt, nkStmtListExpr, nkBlockExpr,
    nkStmtListType, nkBlockType,
    nkWith, nkWithout,
    nkTypeOfExpr, nkObjectTy,
    nkTupleTy, nkTupleClassTy, nkTypeClassTy, nkStaticTy,
    nkRecList, nkRecCase, nkRecWhen,
    nkRefTy, nkPtrTy, nkVarTy,
    nkConstTy, nkOutTy,
    nkDistinctTy,
    nkProcTy,
    nkIteratorTy,         # iterator type
    nkSinkAsgn,
    nkEnumTy,
    nkEnumFieldDef,
    nkArgList, nkPattern
    nkHiddenTryStmt,
    nkClosure,
    nkGotoState,
    nkState,
    nkBreakState,
    nkFuncDef,
    nkTupleConstr,
    nkError,  ## erroneous AST node
    nkModuleRef, nkReplayAction, nkNilRodNode ## internal IC nodes
    nkOpenSym
func toNodeKind*(nnk: NimNodeKind): NodeKind =
  NodeKind(ord(nnk))
func toNimNodeKind*(nk: NodeKind): NimNodeKind =
  NimNodeKind(ord(nk))

type
  NodeTypeKind* = enum
    ntNone, ntBool, ntChar, ntEmpty,
    ntAlias, ntNil, ntExpr, ntStmt,
    ntTypeDesc, ntGenericInvocation, ntGenericBody, ntGenericInst,
    ntGenericParam, ntDistinct, ntEnum, ntOrdinal,
    ntArray, ntObject, ntTuple, ntSet,
    ntRange, ntPtr, ntRef, ntVar,
    ntSequence, ntProc, ntPointer, ntOpenArray,
    ntString, ntCString, ntForward, ntInt,
    ntInt8, ntInt16, ntInt32, ntInt64,
    ntFloat, ntFloat32, ntFloat64, ntFloat128,
    ntUInt, ntUInt8, ntUInt16, ntUInt32, ntUInt64,
    ntUnused0, ntUnused1, ntUnused2,
    ntVarargs,
    ntUncheckedArray,
    ntError,
    ntBuiltintpeClass, ntUserTypeClass, ntUserTypeClassInst,
    ntCompositeTypeClass, ntInferred, ntAnd, ntOr, ntNot,
    ntAnything, ntStatic, ntFromExpr, ntOptDeprecated, ntVoid
func toTypeKind*(tk: NimTypeKind): NodeTypeKind =
  NodeTypeKind(ord(tk))
func toNimTypeKind*(tk: NodeTypeKind): NimTypeKind =
  NimTypeKind(ord(tk))

type
  NodeSymKind* = enum
    nsUnknown, nsConditional, nsDynLib, nsParam,
    nsGenericParam, nsTemp, nsModule, nsType, nsVar, nsLet,
    nsConst, nsResult,
    nsProc, nsFunc, nsMethod, nsIterator,
    nsConverter, nsMacro, nsTemplate, nsField,
    nsEnumField, nsForVar, nsLabel,
    nsStub
func toSymKind*(sk: NimSymKind): NodeSymKind =
  NodeSymKind(ord(sk))
func toNimSymKind*(sk: NodeSymKind): NimSymKind =
  NimSymKind(ord(sk))

const
  STR_LITERALS* = {nkStrLit..nkTripleStrLit, nkCommentStmt, nkIdent, nkSym}
  INT_LITERALS* = {nkCharLit..nkUInt64Lit}
  FLOAT_LITERALS* = {nkFloatLit..nkFloat128Lit}
  ATOMS* = STR_LITERALS + INT_LITERALS + FLOAT_LITERALS + {nkNilLit, nkEmpty}
  CAN_HAVE_CHILDREN* = {low(NodeKind)..high(NodeKind)} - ATOMS

type
  NodeLineInfo* = object
    filename*: string
    line*: int
    column*: int

  Node* {.acyclic.} = object
    repr: string
    info*: NodeLineInfo
    case kind*: NodeKind = NodeKind.nkEmpty
    of STR_LITERALS:
      strVal*: string
    of INT_LITERALS:
      intVal*: BiggestInt
    of FLOAT_LITERALS:
      floatVal*: BiggestFloat
    of CAN_HAVE_CHILDREN:
      children*: seq[Node]
    of nkEmpty, nkNilLit:
      discard

include ./core_converter

proc lineInfoObj*(n: Node): NodeLineInfo =
  ## Get the line info object for node `n`.
  result = n.info

proc newNode*(kind: NodeKind): Node =
  result = Node(kind: kind)
  if kind in CAN_HAVE_CHILDREN:
    result.children = @[]
  # result.kind = kind

proc newTree*(kind: NodeKind; children: varargs[Node]): Node =
  result = newNode(kind)
  if kind notin CAN_HAVE_CHILDREN:
    raise newException(Exception, "Cannot add children to node of kind " & $kind)
  result.children = @[]  # Start with empty seq
  for c in children:
    result.children.add(c)

proc ident*(name: string): Node =
  result = newNode(nkIdent)
  result.strVal = name
proc newIdentNode*(name: string): Node =
  ident(name)

proc newIntLitNode*(i: BiggestInt): Node =
  result = newNode(nkIntLit)
  result.intVal = i

proc newFloatLitNode*(f: BiggestFloat): Node =
  result = newNode(nkFloatLit)
  result.floatVal = f

proc newStrLitNode*(s: string): Node =
  result = newNode(nkStrLit)
  result.strVal = s

proc add*(father: var Node, son: Node) =
  father.children.add(son)

proc add*(father: Node, children: varargs[Node]): Node {.discardable.} =
  result = father
  for son in children:
    result.children.add(son)
  
proc add*(father: var Node, children: varargs[Node]) =
  for son in children:
    father.children.add(son)

proc error(msg: string) = 
  echo "Node Error: ", msg
  raise newException(Exception, msg)

proc error(msg: string, n: Node) = 
  error(msg)

proc hint(parts: varargs[string]) =
  var msg = ""
  for p in parts:
    if msg.len > 0: msg.add("  ")
    msg.add(p)
  echo "Node Hint: ", msg

proc hint(parts: varargs[string], n: Node) =
  hint(parts)

proc bindSym(id: string): Node = 
  result = ident(id)

# proc parseStmt*(s: string): Node =
#   ## Compiles the passed string to its AST representation.
#   ## Expects one or more statements. Raises `ValueError` for parsing errors.
#   result = parseString(s, cache, conf)


# proc repr*(n: Node): string =
#   return n.repr

proc len*(n: Node): int {.inline.} =
  if n.kind notin CAN_HAVE_CHILDREN:
    return 0
  return n.children.len



# NEW CODE:
template `[]`*(n: Node, i: int): Node = 
  if n.kind notin CAN_HAVE_CHILDREN:
    raise newException(IndexDefect, 
      "Cannot access children of node kind " & $n.kind)
  if n.children.len == 0:
    raise newException(IndexDefect, 
      "Cannot access index " & $i & " of empty node (kind: " & $n.kind & ")")
  if i < 0 or i >= n.children.len:
    raise newException(IndexDefect, 
      "Index " & $i & " out of bounds (node has " & $n.children.len & " children)")
  n.children[i]

template `[]=`*(n: Node, i: int; x: Node) =
  if n.kind notin CAN_HAVE_CHILDREN:
    raise newException(IndexDefect, 
      "Cannot set children of node kind " & $n.kind)
  if n.children.len == 0:
    raise newException(IndexDefect, 
      "Cannot set index " & $i & " of empty node (kind: " & $n.kind & ")")
  if i < 0 or i >= n.children.len:
    raise newException(IndexDefect, 
      "Index " & $i & " out of bounds (node has " & $n.children.len & " children)")
  n.children[i] = x


template `[]`*(n: Node, i: BackwardsIndex): Node =
  if n.kind notin CAN_HAVE_CHILDREN:
    raise newException(IndexDefect, 
      "Cannot access children of node kind " & $n.kind)
  let idx = n.children.len - int(i)
  if n.children.len == 0:
    raise newException(IndexDefect, 
      "Cannot access index " & $int(i) & " of empty node (kind: " & $n.kind & ")")
  if idx < 0 or idx >= n.children.len:
    raise newException(IndexDefect, 
      "Index " & $int(i) & " out of bounds (node has " & $n.children.len & " children)")
  n.children[idx]
template `[]=`*(n: Node, i: BackwardsIndex; x: Node) =
  if n.kind notin CAN_HAVE_CHILDREN:
    raise newException(IndexDefect, 
      "Cannot set children of node kind " & $n.kind)
  let idx = n.children.len - int(i)
  if n.children.len == 0:
    raise newException(IndexDefect, 
      "Cannot set index " & $i & " of empty node (kind: " & $n.kind & ")")
  if idx < 0 or idx >= n.children.len:
    raise newException(IndexDefect, 
      "Index " & $i & " out of bounds (node has " & $n.children.len & " children)")
  n.children[idx] = x

# template `[]`*(n: Node, i: BackwardsIndex): Node = n[n.len - i.int]
# template `[]=`*(n: Node, i: BackwardsIndex; x: Node) = n[n.len - i.int] = x

# proc `==`*(a, b: Node): bool {.magic: "EqNimrodNode", noSideEffect.}
#   ## Compare two Nim nodes. Return true if nodes are structurally
#   ## equivalent. This means two independently created nodes can be equal.

# proc sameType*(a, b: Node): bool {.magic: "SameNodeType", noSideEffect.} =
#   ## Compares two Nim nodes' types. Return true if the types are the same,
#   ## e.g. true when comparing alias with original type.
#   discard


template `^^`(n: Node, i: untyped): untyped =
  (when i is BackwardsIndex: n.len - int(i) else: int(i))

proc `[]`*[T, U: Ordinal](n: Node, x: HSlice[T, U]): seq[Node] =
  ## Slice operation for Node.
  ## Returns a seq of child of `n` who inclusive range [n[x.a], n[x.b]].
  let xa = n ^^ x.a
  let L = (n ^^ x.b) - xa + 1
  result = newSeq[Node](L)
  for i in 0..<L:
    result[i] = n[i + xa]

proc `[]=`*(n: var Node, i: BackwardsIndex, child: Node) =
  ## Set `n`'s `i`'th child to `child`.
  n[n.len - i.int] = child

template `or`*(x, y: Node): Node =
  ## Evaluate `x` and when it is not an empty node, return
  ## it. Otherwise evaluate to `y`. Can be used to chain several
  ## expressions to get the first expression that is not empty.
  ##
  ## .. code-block:: nim
  ##
  ##   let node = mightBeEmpty() or mightAlsoBeEmpty() or fallbackNode

  let arg = x
  if arg.kind != nkEmpty:
    arg
  else:
    y

proc expectKind*(n: Node, k: NodeKind) =
  if n.kind != k: error("Expected a node of kind " & $k & ", got " & $n.kind, n)

proc expectMinLen*(n: Node, min: int) =
  if n.len < min: error("Expected a node with at least " & $min & " children, got " & $n.len, n)

proc expectLen*(n: Node, len: int) =
  if n.len != len: error("Expected a node with " & $len & " children, got " & $n.len, n)

proc expectLen*(n: Node, min, max: int) =
  if n.len < min or n.len > max:
    error("Expected a node with " & $min & ".." & $max & " children, got " & $n.len, n)


proc newCall*(theProc: Node, args: varargs[Node]): Node =
  result = newNode(nkCall)
  result.add(theProc)
  result.add(args)

proc newCall*(theProc: string,
              args: varargs[Node]): Node =
  result = newNode(nkCall)
  result.add(newIdentNode(theProc))
  result.add(args)

proc newLit*(c: char): Node =
  result = newNode(nkCharLit)
  result.intVal = ord(c)

proc newLit*(i: int): Node =
  result = newNode(nkIntLit)
  result.intVal = i

proc newLit*(i: int8): Node =
  result = newNode(nkInt8Lit)
  result.intVal = i

proc newLit*(i: int16): Node =
  result = newNode(nkInt16Lit)
  result.intVal = i

proc newLit*(i: int32): Node =
  result = newNode(nkInt32Lit)
  result.intVal = i

proc newLit*(i: int64): Node =
  result = newNode(nkInt64Lit)
  result.intVal = i

proc newLit*(i: uint): Node =
  result = newNode(nkUIntLit)
  result.intVal = BiggestInt(i)

proc newLit*(i: uint8): Node =
  result = newNode(nkUInt8Lit)
  result.intVal = BiggestInt(i)

proc newLit*(i: uint16): Node =
  result = newNode(nkUInt16Lit)
  result.intVal = BiggestInt(i)

proc newLit*(i: uint32): Node =
  result = newNode(nkUInt32Lit)
  result.intVal = BiggestInt(i)

proc newLit*(i: uint64): Node =
  result = newNode(nkUInt64Lit)
  result.intVal = BiggestInt(i)

proc newLit*(b: bool): Node =
  result = if b: bindSym("true") else: bindSym("false")

proc newLit*(s: string): Node =
  result = newNode(nkStrLit)
  result.strVal = s

proc newLit*(f: float32): Node =
  result = newNode(nkFloat32Lit)
  result.floatVal = f

proc newLit*(f: float64): Node =
  result = newNode(nkFloat64Lit)
  result.floatVal = f

when declared(float128):
  proc newLit*(f: float128): Node =
    result = newNode(nkFloat128Lit)
    result.floatVal = f

# import pkg/lifter
func newLit*(arg: static[enum]): Node =
  newCall(
    bindSym($typeof(arg)),
    newLit(ord(arg))
  )

proc newLit*[N,T](arg: array[N,T]): Node
proc newLit*[T](arg: seq[T]): Node
proc newLit*[T](s: set[T]): Node
proc newLit*[T: tuple](arg: T): Node

proc newLit*(arg: object): Node =
  result = nkObjConstr.newTree(arg.typeof.getTypeInst[1])
  for a, b in arg.fieldPairs:
    result.add nkExprColonExpr.newTree( newIdentNode(a), newLit(b) )

proc newLit*(arg: ref object): Node =
  result = nkObjConstr.newTree(arg.typeof.getTypeInst[1])
  for a, b in fieldPairs(arg[]):
    result.add nkExprColonExpr.newTree(newIdentNode(a), newLit(b))

proc newLit*[N,T](arg: array[N,T]): Node =
  result = nkBracket.newTree
  for x in arg:
    result.add newLit(x)

proc newLit*[T](arg: seq[T]): Node =
  let bracket = nkBracket.newTree
  for x in arg:
    bracket.add newLit(x)
  result = nkPrefix.newTree(
    bindSym("@"),
    bracket
  )

proc newLit*[T](s: set[T]): Node =
  result = nkCurly.newTree
  for x in s:
    result.add newLit(x)


proc newLit*[T: tuple](arg: T): Node =
  result = nkTupleConstr.newTree
  when defined(nimHasWorkaround14720) or isNamedTuple(T):
    for a, b in arg.fieldPairs:
      result.add nkExprColonExpr.newTree(newIdentNode(a), newLit(b))
  else:
    for b in arg.fields:
      result.add newLit(b)

proc nestList*(op: Node; pack: Node): Node =
  ## Nests the list `pack` into a tree of call expressions:
  ## `[a, b, c]` is transformed into `op(a, op(c, d))`.
  ## This is also known as fold expression.
  if pack.len < 1:
    error("`nestList` expects a node with at least 1 child")
  result = pack[^1]
  for i in countdown(pack.len - 2, 0):
    result = newCall(op, pack[i], result)

proc nestList*(op: Node; pack: Node; init: Node): Node =
  ## Nests the list `pack` into a tree of call expressions:
  ## `[a, b, c]` is transformed into `op(a, op(c, d))`.
  ## This is also known as fold expression.
  result = init
  for i in countdown(pack.len - 1, 0):
    result = newCall(op, pack[i], result)
proc eqIdent*(lhs, rhs: Node): bool =
  var aNode = lhs
  var bNode = rhs
  
  # Skip nkPostfix and nkAccQuoted wrappers
  if aNode.kind == nkPostfix and aNode.children.len > 1:
    aNode = aNode.children[1]
  if aNode.kind == nkAccQuoted and aNode.children.len > 0:
    aNode = aNode.children[0]
  if bNode.kind == nkPostfix and bNode.children.len > 1:
    bNode = bNode.children[1]
  if bNode.kind == nkAccQuoted and bNode.children.len > 0:
    bNode = bNode.children[0]
  
  # Extract string values
  var aStrVal: string = ""
  var bStrVal: string = ""
  
  case aNode.kind
  of STR_LITERALS:
    aStrVal = aNode.strVal
  of nkOpenSymChoice, nkClosedSymChoice:
    if aNode.children.len > 0 and aNode.children[0].kind in STR_LITERALS:
      aStrVal = aNode.children[0].strVal
  else:
    discard
  
  case bNode.kind
  of STR_LITERALS:
    bStrVal = bNode.strVal
  of nkOpenSymChoice, nkClosedSymChoice:
    if bNode.children.len > 0 and bNode.children[0].kind in STR_LITERALS:
      bStrVal = bNode.children[0].strVal
  else:
    discard
  
  result = 
    if aStrVal.len > 0 and bStrVal.len > 0:
      aStrVal == bStrVal
    else:
      false

proc eqIdent*(lhs: Node, rhs: string): bool =
  eqIdent(lhs, ident rhs)
proc eqIdent*(lhs: string, rhs: Node): bool =
  eqIdent(ident lhs, rhs)
proc eqIdent*(lhs: string, rhs: string): bool =
  eqIdent(ident lhs, ident rhs)

# proc eqIdent*(a: string; b: string): bool {.magic: "EqIdent", noSideEffect.}
#   ## Style insensitive comparison.

# proc eqIdent*(a: Node; b: string): bool {.magic: "EqIdent", noSideEffect.}
#   ## Style insensitive comparison.  `a` can be an identifier or a
#   ## symbol. `a` may be wrapped in an export marker
#   ## (`nkPostfix`) or quoted with backticks (`nkAccQuoted`),
#   ## these nodes will be unwrapped.

# proc eqIdent*(a: string; b: Node): bool {.magic: "EqIdent", noSideEffect.}
#   ## Style insensitive comparison.  `b` can be an identifier or a
#   ## symbol. `b` may be wrapped in an export marker
#   ## (`nkPostfix`) or quoted with backticks (`nkAccQuoted`),
#   ## these nodes will be unwrapped.

# proc eqIdent*(a: Node; b: Node): bool {.magic: "EqIdent", noSideEffect.}
#   ## Style insensitive comparison.  `a` and `b` can be an
#   ## identifier or a symbol. Both may be wrapped in an export marker
#   ## (`nkPostfix`) or quoted with backticks (`nkAccQuoted`),
#   ## these nodes will be unwrapped.

const collapseSymChoice = not defined(nimLegacyMacrosCollapseSymChoice)

proc treeTraverse(n: Node; res: var string; level = 0; isLisp = false, indented = false) =
  if level > 0:
    if indented:
      res.add("\n")
      for i in 0 .. level-1:
        if isLisp:
          res.add(" ")          # dumpLisp indentation
        else:
          res.add("  ")         # dumpTree indentation
    else:
      res.add(" ")

  if isLisp:
    res.add("(")
  res.add(($n.kind).substr(2))

  case n.kind
  of nkEmpty, nkNilLit:
    discard # same as nil node in this representation
  of nkCharLit .. nkInt64Lit:
    res.add(" " & $n.intVal)
  of nkFloatLit .. nkFloat64Lit:
    res.add(" " & $n.floatVal)
  of nkStrLit .. nkTripleStrLit, nkCommentStmt, nkIdent, nkSym:
    res.add(" " & $n.strVal) #.newLit.repr)
  of nkNone:
    assert false
  elif n.kind in {nkOpenSymChoice, nkClosedSymChoice} and collapseSymChoice:
    res.add(" " & $n.len)
    if n.len > 0:
      var allSameSymName = true
      for i in 0..<n.len:
        if n[i].kind != nkSym or not eqIdent(n[i], n[0]):
          allSameSymName = false
          break
      if allSameSymName:
        res.add(" " & $n[0].strVal.newLit.repr)
      else:
        for j in 0 ..< n.len:
          n[j].treeTraverse(res, level+1, isLisp, indented)
  else:
    for j in 0 ..< n.len:
      n[j].treeTraverse(res, level+1, isLisp, indented)

  if isLisp:
    res.add(")")

proc treeRepr*(n: Node): string =
  ## Convert the AST `n` to a human-readable tree-like string.
  ##
  ## See also `repr`, `lispRepr`, and `astGenRepr`.
  result = ""
  n.treeTraverse(result, isLisp = false, indented = true)

proc lispRepr*(n: Node; indented = false): string =
  ## Convert the AST `n` to a human-readable lisp-like string.
  ##
  ## See also `repr`, `treeRepr`, and `astGenRepr`.
  result = ""
  n.treeTraverse(result, isLisp = true, indented = indented)

proc astGenRepr*(n: Node): string =
  ## Convert the AST `n` to the code required to generate that AST.
  ##
  ## See also `repr`, `treeRepr`, and `lispRepr`.

  const
    NodeKinds = {nkEmpty, nkIdent, nkSym, nkNone, nkCommentStmt}
    LitKinds = {nkCharLit..nkInt64Lit, nkFloatLit..nkFloat64Lit, nkStrLit..nkTripleStrLit}

  proc traverse(res: var string, level: int, n: Node) =
    for i in 0..level-1: res.add "  "
    if n.kind in NodeKinds:
      res.add("new" & ($n.kind).substr(3) & "Node(")
    elif n.kind in LitKinds:
      res.add("newLit(")
    elif n.kind == nkNilLit:
      res.add("newNilLit()")
    else:
      res.add($n.kind)

    case n.kind
    of nkEmpty, nkNilLit: discard
    of nkCharLit: res.add("'" & $chr(n.intVal) & "'")
    of nkIntLit..nkInt64Lit: res.add($n.intVal)
    of nkFloatLit..nkFloat64Lit: res.add($n.floatVal)
    of nkStrLit..nkTripleStrLit, nkCommentStmt, nkIdent, nkSym:
      res.add(n.strVal.newLit.repr)
    of nkNone: assert false
    elif n.kind in {nkOpenSymChoice, nkClosedSymChoice} and collapseSymChoice:
      res.add(", # unrepresentable symbols: " & $n.len)
      if n.len > 0:
        res.add(" " & n[0].strVal.newLit.repr)
    else:
      res.add(".newTree(")
      for j in 0..<n.len:
        res.add "\n"
        traverse(res, level + 1, n[j])
        if j != n.len-1:
          res.add(",")

      res.add("\n")
      for i in 0..level-1: res.add "  "
      res.add(")")

    if n.kind in NodeKinds+LitKinds:
      res.add(")")

  result = ""
  traverse(result, 0, n)


proc newEmptyNode*(): Node {.noSideEffect.} =
  ## Create a new empty node.
  result = newNode(nkEmpty)

proc newStmtList*(stmts: varargs[Node]): Node =
  ## Create a new statement list.
  result = newNode(nkStmtList).add(stmts)

proc newPar*(exprs: varargs[Node]): Node =
  ## Create a new parentheses-enclosed expression.
  newNode(nkPar).add(exprs)

proc newBlockStmt*(label, body: Node): Node =
  ## Create a new block statement with label.
  return newNode(nkBlockStmt).add(label, body)

proc newBlockStmt*(body: Node): Node =
  ## Create a new block: stmt.
  return newNode(nkBlockStmt).add(newEmptyNode(), body)

proc newVarStmt*(name, value: Node): Node =
  ## Create a new var stmt.
  return newNode(nkVarSection).add(
    newNode(nkIdentDefs).add(name, newNode(nkEmpty), value))

proc newLetStmt*(name, value: Node): Node =
  ## Create a new let stmt.
  return newNode(nkLetSection).add(
    newNode(nkIdentDefs).add(name, newNode(nkEmpty), value))

proc newConstStmt*(name, value: Node): Node =
  ## Create a new const stmt.
  newNode(nkConstSection).add(
    newNode(nkConstDef).add(name, newNode(nkEmpty), value))

proc newAssignment*(lhs, rhs: Node): Node =
  return newNode(nkAsgn).add(lhs, rhs)

proc newDotExpr*(a, b: Node): Node =
  ## Create new dot expression.
  ## a.dot(b) -> `a.b`
  return newNode(nkDotExpr).add(a, b)

proc newColonExpr*(a, b: Node): Node =
  ## Create new colon expression.
  ## newColonExpr(a, b) -> `a: b`
  newNode(nkExprColonExpr).add(a, b)

proc newIdentDefs*(name, kind: Node;
                   default = newEmptyNode()): Node =
  ## Creates a new `nkIdentDefs` node of a specific kind and value.
  ##
  ## `nkIdentDefs` need to have at least three children, but they can have
  ## more: first comes a list of identifiers followed by a type and value
  ## nodes. This helper proc creates a three node subtree, the first subnode
  ## being a single identifier name. Both the `kind` node and `default`
  ## (value) nodes may be empty depending on where the `nkIdentDefs`
  ## appears: tuple or object definitions will have an empty `default` node,
  ## `let` or `var` blocks may have an empty `kind` node if the
  ## identifier is being assigned a value. Example:
  ##
  ## .. code-block:: nim
  ##
  ##   var varSection = newNode(nkVarSection).add(
  ##     newIdentDefs(ident("a"), ident("string")),
  ##     newIdentDefs(ident("b"), newEmptyNode(), newLit(3)))
  ##   # --> var
  ##   #       a: string
  ##   #       b = 3
  ##
  ## If you need to create multiple identifiers you need to use the lower level
  ## `newNode`:
  ##
  ## .. code-block:: nim
  ##
  ##   result = newNode(nkIdentDefs).add(
  ##     ident("a"), ident("b"), ident("c"), ident("string"),
  ##       newStrLitNode("Hello"))
  newNode(nkIdentDefs).add(name, kind, default)

proc newNilLit*(): Node =
  ## New nil literal shortcut.
  result = newNode(nkNilLit)

proc last*(node: Node): Node = node[node.len-1]
  ## Return the last item in nodes children. Same as `node[^1]`.


const
  RoutineNodes* = {nkProcDef, nkFuncDef, nkMethodDef, nkDo, nkLambda,
                   nkIteratorDef, nkTemplateDef, nkConverterDef, nkMacroDef}
  AtomicNodes* = {nkNone..nkNilLit}
  CallNodes* = {nkCall, nkInfix, nkPrefix, nkPostfix, nkCommand,
    nkCallStrLit, nkHiddenCallConv}

proc expectKind*(n: Node; k: set[NodeKind]) =
  ## Checks that `n` is of kind `k`. If this is not the case,
  ## compilation aborts with an error message. This is useful for writing
  ## macros that check the AST that is passed to them.
  if n.kind notin k:
    error("Expected one of " & $k & ", got " & $n.kind, n)

proc newProc*(name = newEmptyNode();
              params: openArray[Node] = [newEmptyNode()];
              body: Node = newStmtList();
              procType = nkProcDef;
              pragmas: Node = newEmptyNode()): Node =
  ## Shortcut for creating a new proc.
  ##
  ## The `params` array must start with the return type of the proc,
  ## followed by a list of IdentDefs which specify the params.
  if procType notin RoutineNodes:
    error("Expected one of " & $RoutineNodes & ", got " & $procType)
  pragmas.expectKind({nkEmpty, nkPragma})
  result = newNode(procType).add(
    name,
    newEmptyNode(),
    newEmptyNode(),
    newNode(nkFormalParams).add(params),
    pragmas,
    newEmptyNode(),
    body)

proc newIfStmt*(branches: varargs[tuple[cond, body: Node]]): Node =
  ## Constructor for `if` statements.
  ##
  ## .. code-block:: nim
  ##
  ##    newIfStmt(
  ##      (Ident, StmtList),
  ##      ...
  ##    )
  ##
  result = newNode(nkIfStmt)
  if len(branches) < 1:
    error("If statement must have at least one branch")
  for i in branches:
    result.add(newTree(nkElifBranch, i.cond, i.body))

proc newEnum*(name: Node, fields: openArray[Node],
              public, pure: bool): Node =
  ## Creates a new enum. `name` must be an ident. Fields are allowed to be
  ## either idents or EnumFieldDef
  ##
  ## .. code-block:: nim
  ##
  ##    newEnum(
  ##      name    = ident("Colors"),
  ##      fields  = [ident("Blue"), ident("Red")],
  ##      public  = true, pure = false)
  ##
  ##    # type Colors* = Blue Red
  ##
  expectKind name, nkIdent
  if len(fields) < 1:
    raise newException(Exception, "Enum must contain at least one field")
  for field in fields:
    expectKind field, {nkIdent, nkEnumFieldDef}

  let enumBody = newNode(nkEnumTy).add(newEmptyNode()).add(fields)
  var typeDefArgs = [name, newEmptyNode(), enumBody]

  if public:
    let postNode = newNode(nkPostfix).add(
      newIdentNode("*"), typeDefArgs[0])

    typeDefArgs[0] = postNode

  if pure:
    let pragmaNode = newNode(nkPragmaExpr).add(
      typeDefArgs[0],
      add(newNode(nkPragma), newIdentNode("pure")))

    typeDefArgs[0] = pragmaNode

  let
    typeDef   = add(newNode(nkTypeDef), typeDefArgs)
    typeSect  = add(newNode(nkTypeSection), typeDef)

  return typeSect

# proc copyChildrenTo*(src, dest: Node) =
#   ## Copy all children from `src` to `dest`.
#   for i in 0 ..< src.len:
#     dest.add src[i].copyNimTree

template expectRoutine(node: Node) =
  expectKind(node, RoutineNodes)

proc name*(someProc: Node): Node =
  someProc.expectRoutine
  result = someProc[0]
  if result.kind == nkPostfix:
    if result[1].kind == nkAccQuoted:
      result = result[1][0]
    else:
      result = result[1]
  elif result.kind == nkAccQuoted:
    result = result[0]

proc `name=`*(someProc: var Node; val: Node) =
  someProc.expectRoutine
  if someProc[0].kind == nkPostfix:
    someProc[0][1] = val
  else: someProc[0] = val

proc params*(someProc: Node): Node =
  someProc.expectRoutine
  result = someProc[3]
proc `params=`*(someProc: var Node; params: Node) =
  someProc.expectRoutine
  expectKind(params, nkFormalParams)
  someProc[3] = params

proc pragma*(someProc: Node): Node =
  ## Get the pragma of a proc type.
  ## These will be expanded.
  if someProc.kind == nkProcTy:
    result = someProc[1]
  else:
    someProc.expectRoutine
    result = someProc[4]
proc `pragma=`*(someProc: var Node; val: Node) =
  ## Set the pragma of a proc type.
  expectKind(val, {nkEmpty, nkPragma})
  if someProc.kind == nkProcTy:
    someProc[1] = val
  else:
    someProc.expectRoutine
    someProc[4] = val

proc addPragma*(someProc: var Node; pragma: Node) =
  ## Adds pragma to routine definition.
  someProc.expectKind(RoutineNodes + {nkProcTy})
  var pragmaNode = someProc.pragma
  if pragmaNode.kind == nkEmpty:
    pragmaNode = newNode(nkPragma)
    someProc.pragma = pragmaNode
  pragmaNode.add(pragma)

template badNodeKind(n, f) =
  error("Invalid node kind " & $n.kind & " for macros.`" & $f & "`", n)

proc body*(someProc: Node): Node =
  case someProc.kind:
  of nkProcDef, nkFuncDef, nkMethodDef, nkDo, nkLambda, nkIteratorDef, nkTemplateDef, nkConverterDef, nkMacroDef:
    return someProc[6]
  of nkBlockStmt, nkWhileStmt:
    return someProc[1]
  of nkForStmt:
    return someProc.last
  else:
    badNodeKind someProc, "body"

proc `body=`*(someProc: var Node, val: Node) =
  case someProc.kind
  of nkProcDef, nkFuncDef, nkMethodDef, nkDo, nkLambda, nkIteratorDef, nkTemplateDef, nkConverterDef, nkMacroDef:
    someProc[6] = val
  of nkBlockStmt, nkWhileStmt:
    someProc[1] = val
  of nkForStmt:
    someProc[len(someProc)-1] = val
  else:
    badNodeKind someProc, "body="

proc basename*(a: Node): Node =
  ## Pull an identifier from prefix/postfix expressions.
  case a.kind
  of nkIdent: result = a
  of nkPostfix, nkPrefix: result = a[1]
  of nkPragmaExpr: result = basename(a[0])
  else:
    error("Do not know how to get basename of (" & treeRepr(a) & ")\n" &
      repr(a), a)


iterator items*(n: Node): Node {.inline.} =
  ## Iterates over the children of the Node `n`.
  for i in 0 ..< n.len:
    yield n[i]

iterator pairs*(n: Node): (int, Node) {.inline.} =
  ## Iterates over the children of the Node `n` and its indices.
  for i in 0 ..< n.len:
    yield (i, n[i])

iterator children*(n: Node): Node {.inline.} =
  ## Iterates over the children of the Node `n`.
  for i in 0 ..< n.len:
    yield n[i]

template findChild*(n: Node; cond: untyped): Node {.dirty.} =
  ## Find the first child node matching condition (or nil).
  ##
  ## .. code-block:: nim
  ##   var res = findChild(n, it.kind == nkPostfix and
  ##                          it.basename.ident == toNimIdent"foo")
  block:
    var res: Node
    for it in n.children:
      if cond:
        res = it
        break
    res

proc insert*(a: var Node; pos: int; b: Node) =
  ## Insert node `b` into node `a` at `pos`.
  if len(a)-1 < pos:
    # add some empty nodes first
    for i in len(a)-1..pos-2:
      a.add newEmptyNode()
    a.add b
  else:
    # push the last item onto the list again
    # and shift each item down to pos up one
    a.add(a[a.len-1])
    for i in countdown(len(a) - 3, pos):
      a[i + 1] = a[i]
    a[pos] = b

proc `basename=`*(a: var Node; val: string) =
  case a.kind
  of nkIdent:
    a.strVal = val
  of nkPostfix, nkPrefix:
    a[1] = ident(val)
  of nkPragmaExpr: `basename=`(a[0], val)
  else:
    error("Do not know how to get basename of (" & treeRepr(a) & ")\n" &
      repr(a), a)

proc postfix*(node: Node; op: string): Node =
  newNode(nkPostfix).add(ident(op), node)

proc prefix*(node: Node; op: string): Node =
  newNode(nkPrefix).add(ident(op), node)

proc infix*(a: Node; op: string;
            b: Node): Node =
  newNode(nkInfix).add(ident(op), a, b)

proc unpackPostfix*(node: Node): tuple[node: Node; op: string] =
  node.expectKind nkPostfix
  result = (node[1], $node[0])

proc unpackPrefix*(node: Node): tuple[node: Node; op: string] =
  node.expectKind nkPrefix
  result = (node[1], $node[0])

proc unpackInfix*(node: Node): tuple[left: Node; op: string; right: Node] =
  expectKind(node, nkInfix)
  result = (node[1], $node[0], node[2])

# proc copy*(node: Node): Node =
#   ## An alias for `copyNimTree<#copyNimTree,Node>`_.
#   return node.copyNimTree()

proc expectIdent*(n: Node, name: string) =
  ## Check that `eqIdent(n,name)` holds true. If this is not the
  ## case, compilation aborts with an error message. This is useful
  ## for writing macros that check the AST that is passed to them.
  if not eqIdent(n, name):
    error("Expected identifier to be `" & name & "` here", n)

proc hasArgOfName*(params: Node; name: string): bool =
  ## Search `nkFormalParams` for an argument.
  expectKind(params, nkFormalParams)
  for i in 1..<params.len:
    for j in 0..<params[i].len-2:
      if name.eqIdent($params[i][j]):
        return true

proc addIdentIfAbsent*(dest: Node, ident: string) =
  ## Add `ident` to `dest` if it is not present. This is intended for use
  ## with pragmas.
  for node in dest.children:
    case node.kind
    of nkIdent:
      if ident.eqIdent($node): return
    of nkExprColonExpr:
      if ident.eqIdent($node[0]): return
    else: discard
  dest.add(ident(ident))

proc boolVal*(n: Node): bool =
  if n.kind == nkIntLit: n.intVal != 0
  # else: n == bindSym("true") # hacky solution for now
  else: n.strVal == "true"


proc isExported*(n: Node): bool {.noSideEffect.} =
  ## Returns whether the symbol is exported or not.

proc extractDocCommentsAndRunnables*(n: Node): Node =
  ## returns a `nkStmtList` containing the top-level doc comments and
  ## runnableExamples in `a`, stopping at the first child that is neither.
  ## Example:
  ##
  ## .. code-block:: nim
  ##  import std/macros
  ##  macro transf(a): untyped =
  ##    result = quote do:
  ##      proc fun2*() = discard
  ##    let header = extractDocCommentsAndRunnables(a.body)
  ##    # correct usage: rest is appended
  ##    result.body = header
  ##    result.body.add quote do: discard # just an example
  ##    # incorrect usage: nesting inside a nkStmtList:
  ##    # result.body = quote do: (`header`; discard)
  ##
  ##  proc fun*() {.transf.} =
  ##    ## first comment
  ##    runnableExamples: discard
  ##    runnableExamples: discard
  ##    ## last comment
  ##    discard # first statement after doc comments + runnableExamples
  ##    ## not docgen'd

  result = newStmtList()
  for ni in n:
    case ni.kind
    of nkCommentStmt:
      result.add ni
    of nkCall, nkCommand:
      if ni[0].kind == nkIdent and ni[0].eqIdent "runnableExamples":
        result.add ni
      else: break
    else: break


proc copyNodeTree*(n: Node): Node =
  ## Deep copy of a node and its children.
  result = newNode(n.kind)
  case n.kind
  of STR_LITERALS:
    result.strVal = n.strVal
  of INT_LITERALS:
    result.intVal = n.intVal
  of FLOAT_LITERALS:
    result.floatVal = n.floatVal
  of CAN_HAVE_CHILDREN:
    for child in n.children:
      result.add copyNodeTree(child)
  else: discard
proc copyTree*(n: Node): Node =
  ## Deep copy of a node and its children.
  result = copyNodeTree(n)
proc copy*(n: Node): Node =
  ## Deep copy of a node and its children.
  result = copyNodeTree(n)

proc `==`*(a: Node, b: Node): bool {.noSideEffect.} =
  ## Deep comparison of two nodes.
  if a.kind != b.kind: return false
  case a.kind
  of STR_LITERALS:
    return a.strVal == b.strVal
  of INT_LITERALS:
    return a.intVal == b.intVal
  of FLOAT_LITERALS:
    return a.floatVal == b.floatVal
  of CAN_HAVE_CHILDREN:
    if a.len != b.len: return false
    for i in 0..<a.len:
      if not (a[i] == b[i]): return false
    return true
  else:
    return true


import jsony
import strutils
proc dumpHook*(s: var string, v: Node) =
  s.add '{'
  s.add "\"kind\":"
  s.dumpHook($v.kind)
  
  case v.kind
  of STR_LITERALS:
    s.add ",\"strVal\":"
    s.dumpHook(v.strVal)
  of INT_LITERALS:
    s.add ",\"intVal\":"
    s.dumpHook(v.intVal)
  of FLOAT_LITERALS:
    s.add ",\"floatVal\":"
    s.dumpHook(v.floatVal)
  of CAN_HAVE_CHILDREN:
    s.add ",\"children\":"
    s.dumpHook(v.children)
  of nkEmpty, nkNilLit:
    discard
  
  s.add '}'

proc parseHook*(s: string, i: var int, v: var Node) =
  var kind: string
  var strVal: string
  var intVal: BiggestInt
  var floatVal: BiggestFloat
  var children: seq[Node]
  
  # Parse the JSON object
  eatSpace(s, i)
  eatChar(s, i, '{')
  
  while i < s.len:
    eatSpace(s, i)
    if s[i] == '}':
      inc i
      break
    
    var key: string
    parseHook(s, i, key)
    eatSpace(s, i)
    eatChar(s, i, ':')
    eatSpace(s, i)
    
    case key
    of "kind":
      parseHook(s, i, kind)
    of "strVal":
      parseHook(s, i, strVal)
    of "intVal":
      parseHook(s, i, intVal)
    of "floatVal":
      parseHook(s, i, floatVal)
    of "children":
      parseHook(s, i, children)
    else:
      # Skip unknown fields
      skipValue(s, i)
    
    eatSpace(s, i)
    if i < s.len and s[i] == ',':
      inc i
  
  # Construct the Node with the right variant
  let nodeKind = parseEnum[NodeKind](kind)
  v = Node(kind: nodeKind)
  
  case v.kind
  of STR_LITERALS:
    v.strVal = strVal
  of INT_LITERALS:
    v.intVal = intVal
  of FLOAT_LITERALS:
    v.floatVal = floatVal
  of CAN_HAVE_CHILDREN:
    v.children = children
  of nkEmpty, nkNilLit:
    discard


proc repr*(n: Node, indent: int = 0): string =
  ## Generate the Nim code representation of a Node with proper indentation.
  ## Converts AST back to source code through recursion.
  ## 
  ## Args:
  ##   n: The node to represent
  ##   indent: Current indentation level (number of spaces)
  
  let ind = "  ".repeat(indent)  # Current line indentation
  
  case n.kind
  # ============================================================
  # LITERALS
  # ============================================================
  of nkNilLit:
    result = "nil"
  
  of nkIntLit, nkInt8Lit, nkInt16Lit, nkInt32Lit, nkInt64Lit,
     nkUIntLit, nkUInt8Lit, nkUInt16Lit, nkUInt32Lit, nkUInt64Lit:
    result = $n.intVal
  
  of nkFloatLit, nkFloat32Lit, nkFloat64Lit, nkFloat128Lit:
    result = $n.floatVal
  
  of nkStrLit, nkRStrLit, nkTripleStrLit:
    result = "\"" & n.strVal & "\""
  
  of nkCharLit:
    result = "'" & $char(n.intVal) & "'"
  
  of nkIdent, nkSym:
    result = n.strVal
  
  of nkCommentStmt:
    result = "# " & n.strVal
  
  of nkEmpty:
    result = ""
  
  # ============================================================
  # OPERATORS
  # ============================================================
  of nkPrefix:
    if n.len >= 2:
      result = repr(n[0], indent) & repr(n[1], indent)
  
  of nkPostfix:
    if n.len >= 2:
      result = repr(n[1], indent) & repr(n[0], indent)
  
  of nkInfix:
    if n.len >= 3:
      result = repr(n[1], indent) & " " & repr(n[0], indent) & " " & repr(n[2], indent)
  
  # ============================================================
  # CALLS AND ACCESS
  # ============================================================
  of nkCall, nkCommand:
    if n.len > 0:
      result = repr(n[0], indent)
      if n.len > 1:
        result.add "("
        for i in 1..<n.len:
          if i > 1: result.add ", "
          result.add repr(n[i], indent)
        result.add ")"
  
  of nkDotExpr:
    if n.len >= 2:
      result = repr(n[0], indent) & "." & repr(n[1], indent)
  
  of nkBracketExpr:
    if n.len > 0:
      result = repr(n[0], indent)
      if n.len > 1:
        result.add "["
        for i in 1..<n.len:
          if i > 1: result.add ", "
          result.add repr(n[i], indent)
        result.add "]"
  
  # ============================================================
  # COLLECTIONS
  # ============================================================
  of nkPar, nkTupleConstr:
    result = "("
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
    result.add ")"
  
  of nkBracket:
    result = "["
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
    result.add "]"
  
  of nkCurly:
    result = "{"
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
    result.add "}"
  
  # ============================================================
  # STATEMENTS (WITH INDENTATION!)
  # ============================================================
  of nkStmtList, nkStmtListExpr:
    for i in 0..<n.len:
      if i > 0: result.add "\n"
      if n[i].kind != nkEmpty:
        result.add "  ".repeat(indent) & repr(n[i], indent)
  
  of nkAsgn, nkFastAsgn, nkSinkAsgn:
    if n.len >= 2:
      result = repr(n[0], indent) & " = " & repr(n[1], indent)
  
  of nkExprColonExpr:
    if n.len >= 2:
      result = repr(n[0], indent) & ": " & repr(n[1], indent)
  
  of nkExprEqExpr:
    if n.len >= 2:
      result = repr(n[0], indent) & " = " & repr(n[1], indent)
  
  # ============================================================
  # PROCEDURE DEFINITIONS (WITH INDENTATION!)
  # ============================================================
  of nkProcDef, nkFuncDef, nkMethodDef, nkConverterDef, nkIteratorDef:
    if n.len >= 7:
      let keyword = case n.kind
        of nkProcDef: "proc"
        of nkFuncDef: "func"
        of nkMethodDef: "method"
        of nkConverterDef: "converter"
        of nkIteratorDef: "iterator"
        else: "proc"
      result = keyword & " " & repr(n[0], indent)
      if n[3].kind != nkEmpty:
        result.add repr(n[3], indent)
      # Add pragmas if present
      if n.len > 4 and n[4].kind != nkEmpty:
        result.add " " & repr(n[4], indent)
      if n[6].kind != nkEmpty:
        result.add " =\n"
        result.add repr(n[6], indent + 1)  # Indent body!
  
  of nkFormalParams:
    result = "("
    var first = true
    for i in 1..<n.len:
      if not first: result.add ", "
      first = false
      result.add repr(n[i], indent)
    result.add ")"
    if n.len > 0 and n[0].kind != nkEmpty:
      result.add ": " & repr(n[0], indent)
  
  of nkIdentDefs, nkConstDef:
    if n.len >= 3:
      for i in 0..<n.len-2:
        if i > 0: result.add ", "
        result.add repr(n[i], indent)
      if n[^2].kind != nkEmpty:
        result.add ": " & repr(n[^2], indent)
      if n[^1].kind != nkEmpty:
        result.add " = " & repr(n[^1], indent)
  
  of nkVarSection, nkLetSection, nkConstSection:
    let keyword = case n.kind
      of nkVarSection: "var"
      of nkLetSection: "let"
      of nkConstSection: "const"
      else: ""
    for i in 0..<n.len:
      if i > 0: result.add "\n"
      result.add keyword & " " & repr(n[i], indent)
  
  # ============================================================
  # CONTROL FLOW (WITH INDENTATION!)
  # ============================================================
  of nkIfStmt, nkIfExpr:
    for i in 0..<n.len:
      if i == 0:
        result.add "if "
      result.add repr(n[i], indent)
  
  of nkElifBranch, nkElifExpr:
    if n.len >= 2:
      result = "elif " & repr(n[0], indent) & ":\n"
      result.add repr(n[1], indent + 1)  # Indent body!
  
  of nkElse, nkElseExpr:
    result = "else:\n"
    if n.len >= 1:
      result.add repr(n[0], indent + 1)  # Indent body!
    else:
      result.add "  ".repeat(indent + 1) & "discard"
  
  of nkWhileStmt:
    if n.len >= 2:
      result = "while " & repr(n[0], indent) & ":\n"
      result.add repr(n[1], indent + 1)  # Indent body!
  
  of nkForStmt:
    if n.len >= 3:
      result = "for "
      for i in 0..<n.len-2:
        if i > 0: result.add ", "
        result.add repr(n[i], indent)
      result.add " in " & repr(n[^2], indent) & ":\n"
      result.add repr(n[^1], indent + 1)  # Indent body!
  
  of nkCaseStmt:
    if n.len > 0:
      result = "case " & repr(n[0], indent) & ":"
      for i in 1..<n.len:
        result.add "\n"
        result.add repr(n[i], indent)  # Branches handle their own indentation
  
  of nkOfBranch:
    if n.len >= 2:
      result = "  ".repeat(indent) & "of "
      for i in 0..<n.len-1:
        if i > 0: result.add ", "
        result.add repr(n[i], indent)
      result.add ":\n"
      result.add repr(n[^1], indent + 1)  # Indent body!
  
  of nkReturnStmt:
    result = "return"
    if n.len > 0 and n[0].kind != nkEmpty:
      result.add " " & repr(n[0], indent)
  
  of nkYieldStmt:
    result = "yield"
    if n.len > 0 and n[0].kind != nkEmpty:
      result.add " " & repr(n[0], indent)
  
  of nkBreakStmt:
    result = "break"
    if n.len > 0 and n[0].kind != nkEmpty:
      result.add " " & repr(n[0], indent)
  
  of nkContinueStmt:
    result = "continue"
  
  of nkBlockStmt, nkBlockExpr:
    result = "block"
    if n.len >= 1 and n[0].kind != nkEmpty:
      result.add " " & repr(n[0], indent)
    if n.len >= 2:
      result.add ":\n"
      result.add repr(n[1], indent + 1)  # Indent body!
  
  of nkDiscardStmt:
    result = "discard"
    if n.len > 0 and n[0].kind != nkEmpty:
      result.add " " & repr(n[0], indent)
  
  # ============================================================
  # OBJECT CONSTRUCTION
  # ============================================================
  of nkObjConstr:
    if n.len > 0:
      result = repr(n[0], indent)
      if n.len > 1:
        result.add "("
        for i in 1..<n.len:
          if i > 1: result.add ", "
          result.add repr(n[i], indent)
        result.add ")"
  
  # ============================================================
  # LAMBDAS (WITH INDENTATION!)
  # ============================================================
  of nkLambda, nkDo:
    result = "proc"
    if n.len >= 4 and n[3].kind != nkEmpty:
      result.add repr(n[3], indent)
    if n.len >= 7 and n[6].kind != nkEmpty:
      result.add " =\n"
      result.add repr(n[6], indent + 1)  # Indent body!
  
  # ============================================================
  # PRAGMAS
  # ============================================================
  of nkPragma:
    result = "{"
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
    result.add "}"
  
  of nkPragmaExpr:
    if n.len >= 2:
      result = repr(n[0], indent) & " " & repr(n[1], indent)
  
  # ============================================================
  # TYPE DEFINITIONS (WITH INDENTATION!)
  # ============================================================
  of nkTypeSection:
    result = "type"
    for i in 0..<n.len:
      result.add "\n"
      result.add "  ".repeat(indent + 1) & repr(n[i], indent + 1)
  
  of nkTypeDef:
    if n.len >= 3:
      result = repr(n[0], indent)
      if n[1].kind != nkEmpty:
        result.add repr(n[1], indent)
      if n[2].kind != nkEmpty:
        result.add " = " & repr(n[2], indent)
  
  of nkObjectTy:
    result = "object"
    if n.len >= 1 and n[0].kind != nkEmpty:
      result.add " of " & repr(n[0], indent)
    if n.len >= 3 and n[2].kind != nkEmpty:
      result.add "\n"
      result.add repr(n[2], indent + 1)  # Indent fields!
  
  of nkRecList:
    for i in 0..<n.len:
      if i > 0: result.add "\n"
      result.add "  ".repeat(indent) & repr(n[i], indent)
  
  of nkRecCase:
    if n.len >= 2:
      result = "case " & repr(n[0], indent)
      for i in 1..<n.len:
        result.add "\n"
        result.add repr(n[i], indent)
  
  of nkRecWhen:
    if n.len >= 2:
      result = "when " & repr(n[0], indent) & ":\n"
      result.add repr(n[1], indent + 1)
  
  of nkEnumTy:
    result = "enum"
    for i in 0..<n.len:
      if n[i].kind != nkEmpty:
        result.add "\n"
        result.add "  ".repeat(indent + 1) & repr(n[i], indent + 1)
  
  of nkEnumFieldDef:
    if n.len >= 2:
      result = repr(n[0], indent) & " = " & repr(n[1], indent)
    elif n.len >= 1:
      result = repr(n[0], indent)
  
  # ============================================================
  # TYPE EXPRESSIONS
  # ============================================================
  of nkRefTy:
    if n.len >= 1:
      result = "ref " & repr(n[0], indent)
  
  of nkPtrTy:
    if n.len >= 1:
      result = "ptr " & repr(n[0], indent)
  
  of nkVarTy:
    if n.len >= 1:
      result = "var " & repr(n[0], indent)
  
  of nkTupleTy:
    result = "tuple["
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
    result.add "]"
  
  of nkProcTy:
    result = "proc"
    if n.len >= 1 and n[0].kind != nkEmpty:
      result.add repr(n[0], indent)
  
  # ============================================================
  # IMPORTS
  # ============================================================
  of nkImportStmt:
    result = "import "
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
  
  of nkExportStmt:
    result = "export "
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
  
  of nkFromStmt:
    if n.len >= 2:
      result = "from " & repr(n[0], indent) & " import "
      for i in 1..<n.len:
        if i > 1: result.add ", "
        result.add repr(n[i], indent)
  
  of nkIncludeStmt:
    result = "include "
    for i in 0..<n.len:
      if i > 0: result.add ", "
      result.add repr(n[i], indent)
  
  # ============================================================
  # CONVERSIONS
  # ============================================================
  of nkConv, nkHiddenStdConv, nkHiddenSubConv:
    if n.len >= 2:
      result = repr(n[0], indent) & "(" & repr(n[1], indent) & ")"
  
  of nkCast:
    if n.len >= 2:
      result = "cast[" & repr(n[0], indent) & "](" & repr(n[1], indent) & ")"
  
  of nkAddr:
    if n.len >= 1:
      result = "addr " & repr(n[0], indent)
  
  # ============================================================
  # TRY/EXCEPT (WITH INDENTATION!)
  # ============================================================
  of nkTryStmt:
    if n.len > 0:
      result = "try:\n"
      result.add repr(n[0], indent + 1)  # Indent body!
      for i in 1..<n.len:
        result.add "\n"
        result.add repr(n[i], indent)
  
  of nkExceptBranch:
    result = "  ".repeat(indent) & "except"
    if n.len >= 2:
      for i in 0..<n.len-1:
        if i > 0: result.add ", "
        else: result.add " "
        result.add repr(n[i], indent)
      result.add ":\n"
      result.add repr(n[^1], indent + 1)  # Indent body!
    elif n.len == 1:
      result.add ":\n"
      result.add repr(n[0], indent + 1)
  
  of nkFinally:
    if n.len >= 1:
      result = "  ".repeat(indent) & "finally:\n"
      result.add repr(n[0], indent + 1)  # Indent body!
  
  # ============================================================
  # DEFAULT
  # ============================================================
  else:
    # For unhandled node kinds, try to show children
    if n.kind in CAN_HAVE_CHILDREN and n.len > 0:
      for i in 0..<n.len:
        if i > 0: result.add " "
        result.add repr(n[i], indent)
    else:
      result = ""

proc `$`*(node: Node): string =
  return node.repr
  # ## Get the string of an identifier node.
  # case node.kind
  # of nkPostfix:
  #   result = node.basename.strVal & "*"
  # of nkStrLit..nkTripleStrLit, nkCommentStmt, nkSym, nkIdent:
  #   result = node.strVal
  # of nkOpenSymChoice, nkClosedSymChoice:
  #   result = $node[0]
  # of nkAccQuoted:
  #   result = $node[0]
  # of nkStmtList:
  #   result = ""
  #   for child in node.children:
  #     if result.len > 0:
  #       result.add("\n")
  #     result.add($child)
  # else:
  #   badNodeKind node, "$"