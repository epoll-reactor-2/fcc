//fun main():
//       0:   int t0
//       1:   t0.0 = 0
//            | t0.2 = φ(2, 1)
//            | t1.1 = φ(2, 1)
//            | t2.2 = φ(2, 1)
//       2:   | int t1
//       3:   | t1.0 = t0.0 < 10
//       4:   | if t1.0 != 0 goto L6
//       5:   | jmp L11
//       6:   | int t2
//       7:   | t2.0 = t0.0
//       8:   | t2.1 = t2.0 + 1
//       9:   | t0.1 = t0.0 + 1
//      10:   | jmp L2
//      11:   ret t0.0
int main() {
    int i = 0;
    while (i < 10) {
        int j = i;
        ++j;
        ++i;
    }
    return i;
}