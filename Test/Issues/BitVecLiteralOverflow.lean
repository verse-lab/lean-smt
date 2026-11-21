import Smt

example : (5#2 : BitVec 2) = 1#2 := by
  smt

example : (4 : BitVec 2) = 0#2 := by
  smt

example : True := by
  fail_if_success
    suffices (5#2 : BitVec 2) = 2#2 from trivial
    smt +trust
  trivial
