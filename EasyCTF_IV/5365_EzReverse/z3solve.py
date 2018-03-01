import z3
import string

flag = ""

char1 = z3.Int("char1")
char2 = z3.Int("char2")
char3 = z3.Int("char3")
char4 = z3.Int("char4")
char5 = z3.Int("char5")

s = z3.Solver()

s.add(char1 + 1 == char5 + 5 - 0xa)
s.add(char2 + 2 == 0x35)
s.add(char3 + 3 == char4 + 4 + 0xe)
s.add(char4 + 4 == 0x6f)
s.add(char5 + 5 == char4 + 4 + 0x3)

while s.check() != z3.sat:
    if s.check == z3.unsat:
        print("No solution found")
    else:
        for k, v in s.statistics():
            print("%s : %s" % (k, v))


flag += chr(s.model()[char1].as_long())
flag += chr(s.model()[char2].as_long())
flag += chr(s.model()[char3].as_long())
flag += chr(s.model()[char4].as_long())
flag += chr(s.model()[char5].as_long())

print(flag)
