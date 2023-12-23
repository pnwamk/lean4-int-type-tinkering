import «IntTypeTinkering»

def x : Int8 := 42

def y  : Int8 := x * 2

def addInt8s(a b : Int8) : Int8 :=
  a + b

def main : IO Unit :=
  IO.println s!"Hello, world! {addInt8s x y}"
