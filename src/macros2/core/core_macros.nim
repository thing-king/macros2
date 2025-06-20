import core
import macros
import strutils

# TODO:  implement line info
macro error*(args: varargs[untyped]): untyped =
  result = macros.newTree(macros.nnkStmtList,
    macros.newTree(macros.nnkCall,
      macros.ident("echo"),
      macros.newStrLitNode("ERROR!")
    ),
    macros.newTree(macros.nnkCall,
      macros.ident("quit"),
      macros.newIntLitNode(1)
    )
  )

  # echo "ERROR!"
  # quit(1)
  # var strs: seq[string] = @[]
  # for a in args:
  #   if a.kind == macros.nnkIdent:
  #     continue
  #   if a.kind != macros.nnkStrLit:
  #     macros.error("error macro only accepts string literals or a NimNode, got: " & $a.kind, a)
  #     continue
  #   strs.add(a.strVal)

  # result = macros.newTree(macros.nnkRaiseStmt,
  #   macros.newTree(macros.nnkCall,
  #     macros.newIdentNode("newException"),
  #     macros.newIdentNode("ValueError"),
  #     macros.newStrLitNode(strs.join(",  "))
  #   )
  # )
macro warning*(args: varargs[untyped]): untyped =
  # var strs: seq[string] = @[]
  # for a in args:
  #   if a.kind == macros.nnkIdent:
  #     continue
  #   if a.kind != macros.nnkStrLit:
  #     macros.error("warning macro only accepts string literals or a NimNode")
  #     continue
  #   strs.add(a.strVal)

  # result = macros.newTree(macros.nnkCall,
  #     macros.newIdentNode("echo"),
  #     macros.newStrLitNode("Warning: " & strs.join(",  "))
  # )
  result = macros.newTree(macros.nnkCall, macros.ident("echo"), macros.newStrLitNode("Warning: "))
  for a in args:
    result.add(
      macros.newTree(
        macros.nnkPrefix,
        macros.ident("$"),
        a
      )
    )
macro hint*(args: varargs[untyped]): untyped =
  # # result = macros.newTree(macros.nnkCall, macros.ident("echo"))
  # # for a in args:
  # #   result.add(a)
  # var strs: seq[string] = @[]
  # for a in args:
  #   if a.kind == macros.nnkIdent:
  #     continue
  #   if a.kind != macros.nnkStrLit:
  #     macros.error("hint macro only accepts string literals or a NimNode")
  #     continue
  #   strs.add(a.strVal)
  # result = macros.newTree(macros.nnkCall,
  #     macros.newIdentNode("echo"),
  #     macros.newStrLitNode("Hint: " & strs.join(",  "))
  # )

  result = macros.newTree(macros.nnkCall, macros.ident("echo"), macros.newStrLitNode("Hint: "))
  for a in args:
    result.add(
      macros.newTree(
        macros.nnkPrefix,
        macros.ident("$"),
        a
      )
    )