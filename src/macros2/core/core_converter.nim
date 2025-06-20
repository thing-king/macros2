import system except NimNode
import ./core

import compiler/ast

proc toCompilerNode*(n: system.NimNode): PNode =
  ## "Converts" system.NimNode to PNode
  ## In reality, this is a no-op cast since they're the same type
  result = cast[PNode](n)

proc fromCompilerNode*(n: PNode): system.NimNode =
  ## "Converts" PNode back to system.NimNode  
  result = cast[system.NimNode](n)