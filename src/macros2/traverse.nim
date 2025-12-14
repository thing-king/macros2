import macros, strutils

import pkg/debug
import pkg/colors

macro traverseNode*(nodeIdent, astBody, iteratorName, skipKinds: untyped, 
                handler: untyped): untyped =
  let processNode = iteratorName
  
  # Build the skip condition from the untyped node
  var skipCondition: NimNode
  if skipKinds.kind != nnkEmpty and skipKinds.kind != nnkNilLit:
    # Extract string literals and build a string set for comparison
    var kindStrings: seq[string] = @[]
    
    case skipKinds.kind
    of nnkPrefix:
      if skipKinds[0].kind == nnkIdent and skipKinds[0].strVal == "@":
        let bracket = skipKinds[1]
        if bracket.kind == nnkBracket:
          for node in bracket:
            if node.kind == nnkStrLit:
              kindStrings.add(node.strVal)
    of nnkBracket:
      for node in skipKinds:
        if node.kind == nnkStrLit:
          kindStrings.add(node.strVal)
    else:
      error("skipKinds must be a sequence literal", skipKinds)
    
    if kindStrings.len > 0:
      # Build array literal for string comparison: $node.kind in ["nnkProcDef", "nnkFuncDef"]
      var kindArray = nnkBracket.newTree()
      for kindStr in kindStrings:
        kindArray.add(newStrLitNode(kindStr))
      
      skipCondition = infix(
        nnkPrefix.newTree(ident("$"), nnkDotExpr.newTree(nodeIdent, ident("kind"))),
        "in",
        kindArray
      )
    else:
      skipCondition = newLit(false)
  else:
    skipCondition = newLit(false)
  
  # Use genSym for unique identifiers
  let modifiedBodySym = genSym(nskVar, "modifiedBody")
  let iSym = genSym(nskForVar, "i")
  let startNodeSym = genSym(nskVar, "startNode")
  let childSym = genSym(nskVar, "child")
  let iSym2 = genSym(nskForVar, "i")
  let originalNodeSym = genSym(nskLet, "originalNode")
  
  # Manually construct the proc to avoid quote do: symbol binding issues
  let procBody = nnkStmtList.newTree(
    nnkIfStmt.newTree(
      nnkElifBranch.newTree(
        nnkDotExpr.newTree(nodeIdent, ident("isEmpty")),
        nnkStmtList.newTree(nnkReturnStmt.newTree(newEmptyNode()))
      )
    ),
    # let originalNode = nodeIdent
    nnkLetSection.newTree(
      nnkIdentDefs.newTree(
        originalNodeSym,
        newEmptyNode(),
        nodeIdent
      )
    ),
    # handler
    handler,
    # if originalNode != nodeIdent: return
    nnkIfStmt.newTree(
      nnkElifBranch.newTree(
        infix(originalNodeSym, "!=", nodeIdent),
        nnkStmtList.newTree(nnkReturnStmt.newTree(newEmptyNode()))
      )
    ),
    # if skipCondition: return
    nnkIfStmt.newTree(
      nnkElifBranch.newTree(
        skipCondition,
        nnkStmtList.newTree(nnkReturnStmt.newTree(newEmptyNode()))
      )
    ),
    # if nodeIdent.len > 0: ...
    nnkIfStmt.newTree(
      nnkElifBranch.newTree(
        infix(nnkDotExpr.newTree(nodeIdent, ident("len")), ">", newLit(0)),
        nnkStmtList.newTree(
          nnkForStmt.newTree(
            iSym,
            infix(newLit(0), "..<", nnkDotExpr.newTree(nodeIdent, ident("len"))),
            nnkStmtList.newTree(
              nnkVarSection.newTree(
                nnkIdentDefs.newTree(
                  childSym,
                  newEmptyNode(),
                  nnkBracketExpr.newTree(nodeIdent, iSym)
                )
              ),
              nnkIfStmt.newTree(
                nnkElifBranch.newTree(
                  prefix(nnkDotExpr.newTree(childSym, ident("isEmpty")), "not"),
                  nnkStmtList.newTree(
                    nnkCall.newTree(processNode, childSym),
                    nnkAsgn.newTree(
                      nnkBracketExpr.newTree(nodeIdent, iSym),
                      childSym
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  
  let procDef = nnkProcDef.newTree(
    processNode,
    newEmptyNode(),
    newEmptyNode(),
    nnkFormalParams.newTree(
      newEmptyNode(),
      nnkIdentDefs.newTree(
        nodeIdent,
        nnkVarTy.newTree(ident("Node")),
        newEmptyNode()
      )
    ),
    newEmptyNode(),
    newEmptyNode(),
    procBody
  )
  
  result = nnkStmtList.newTree(
    procDef,
    nnkVarSection.newTree(
      nnkIdentDefs.newTree(
        modifiedBodySym,
        newEmptyNode(),
        astBody
      )
    ),
    nnkForStmt.newTree(
      iSym2,
      infix(newLit(0), "..<", nnkDotExpr.newTree(modifiedBodySym, ident("len"))),
      nnkStmtList.newTree(
        nnkVarSection.newTree(
          nnkIdentDefs.newTree(
            startNodeSym,
            newEmptyNode(),
            nnkBracketExpr.newTree(modifiedBodySym, iSym2)
          )
        ),
        nnkIfStmt.newTree(
          nnkElifBranch.newTree(
            prefix(nnkDotExpr.newTree(startNodeSym, ident("isEmpty")), "not"),
            nnkStmtList.newTree(
              nnkCall.newTree(processNode, startNodeSym),
              nnkAsgn.newTree(
                nnkBracketExpr.newTree(modifiedBodySym, iSym2),
                startNodeSym
              )
            )
          )
        )
      )
    ),
    modifiedBodySym
  )
  # echo result.repr