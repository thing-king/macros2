import macros
import strutils



proc intToLetter(n: int): string =
  ($(char(ord('A') + n))).toLowerAscii

macro exportMacro*(sym: typed): untyped =
  # detect if `prc` (sym, or proc) is a proc
  if sym.kind != nnkSym:
    error("exportMacro only works on proc names (idents)", sym)
  if sym.symKind != nskProc:
    error("exportMacro only works on proc names (idents)", sym)

  # # resolve the symbol to a proc
  let typ = getType(sym)
  # echo typ.treeRepr

  if typ.kind != nnkBracketExpr:
    error("exportMacro only works on proc names (idents)", sym)
  
  let outputTyp = typ[1]
  proc isNimNodeType(n: NimNode): bool =
    if n.kind != nnkBracketExpr:
      return false
    if n.len != 2:
      return false
    return n[0].kind == nnkSym and n[0].strVal == "ref" and n[1].kind == nnkSym and n[1].strVal == "TNode"

  if not isNimNodeType(outputTyp):
    error("exportMacro only works on procs that return macros2.NimNode, got: " & $outputTyp, sym)

  var paramTyps: seq[NimNode] = @[]
  for i in 2 ..< typ.len:
    if typ[i].kind != nnkBracketExpr:
      error("exportMacro only works on procs with macros2.NimNode params, got: " & $typ[i], sym)
    paramTyps.add(typ[i])

  let procNameIdent = ident(sym.strVal & "FFI")
  var formalParams = nnkFormalParams.newTree(
    newIdentNode("cstring"),
  )
  var body = nnkDotExpr.newTree(
    nnkCall.newTree(
      sym,
    ),
    newIdentNode("repr")
  )

  # loop for each len of paramTyps
  for i in 0 ..< paramTyps.len:
    let nameIdent = ident(intToLetter(i))
    formalParams.add(
      nnkIdentDefs.newTree(
        nameIdent,
        newIdentNode("cstring"),
        newEmptyNode()
      )
    )
    body[0].add(
      nnkCall.newTree(
        newIdentNode("parseStmt"),
        nnkPrefix.newTree(
          newIdentNode("$"),
          nameIdent
        )
      )
    )

  result = nnkProcDef.newTree(
    nnkPostfix.newTree(
      newIdentNode("*"),
      procNameIdent
    ),
    newEmptyNode(),
    newEmptyNode(),
    formalParams,
    nnkPragma.newTree(
      newIdentNode("exportc"),
      newIdentNode("dynlib")
    ),
    newEmptyNode(),
    body
  )

  echo result.repr

  # echo $paramTyps.len

  # echo $prc.symKind


proc importMacroCore(nameIdent: NimNode, params: seq[NimNode]): NimNode =
  if nameIdent.kind != nnkIdent:
    error "Expected an identifier for the macro name", nameIdent
  let macroName = nameIdent.strVal
  let ffiMacroName = macroName & "FFI"
  let procNameIdent = newIdentNode(macroName & "Lib")

  var formalParams = nnkFormalParams.newTree(
    newIdentNode("untyped"),
  )
  var procFormalParams = nnkFormalParams.newTree(
    newIdentNode("cstring"),
    # nnkIdentDefs.newTree(
    #   newIdentNode("x"),
    #   newIdentNode("int"),
    #   newEmptyNode()
    # )
  )
  var body = nnkStmtList.newTree(
    nnkReturnStmt.newTree(
      nnkCall.newTree(
        bindSym("parseStmt"),
        nnkPrefix.newTree(
          ident("$"),
          nnkCall.newTree(
            procNameIdent
          )
        )
      )
    )
  )
  for i in 0 ..< params.len:
    if params[i].kind != nnkIdent:
      error "Expected an identifier for the macro param", params[i]
    let name = intToLetter(i)
    procFormalParams.add(
      nnkIdentDefs.newTree(
        newIdentNode(name),
        newIdentNode("cstring"),
        newEmptyNode()
      )
    )

    let macroParamIdent = ident(name)
    formalParams.add(
      nnkIdentDefs.newTree(
        macroParamIdent,
        newIdentNode("untyped"),
        newEmptyNode()
      )
    )
    body[0][0][1][1].add(
      nnkDotExpr.newTree(
        macroParamIdent,
        newIdentNode("repr")
      )
    )

  result = nnkStmtList.newTree(
    nnkProcDef.newTree(
      procNameIdent,
      newEmptyNode(),
      newEmptyNode(),
      procFormalParams,
      nnkPragma.newTree(
        nnkExprColonExpr.newTree(
          newIdentNode("importc"),
          newLit(ffiMacroName)
        ),
        nnkExprColonExpr.newTree(
          newIdentNode("dynlib"),
          newLit(macroName & ".so")
        )
      ),
      newEmptyNode(),
      newEmptyNode()
    ),

    nnkMacroDef.newTree(
      nnkPostfix.newTree(
        newIdentNode("*"),
        newIdentNode(macroName)
      ),
      newEmptyNode(),
      newEmptyNode(),
      formalParams,
      newEmptyNode(),
      newEmptyNode(),
      body
      # quote do:
      #   return newEmptyNode()
    )
  )
  echo result.repr

macro importMacro*(nameIdent: untyped): untyped =
  importMacroCore(nameIdent, @[])
macro importMacro*(nameIdent: untyped, params: untyped): untyped =
  var paramSeq: seq[NimNode] = @[]
  if params.kind != nnkTupleConstr:
    error "Expected a tuple of idents", params
  for p in params:
    paramSeq.add(p)
  importMacroCore(nameIdent, paramSeq)


# makeMacro myProtectedMacro, "protectedMacro"