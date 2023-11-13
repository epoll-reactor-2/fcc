//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | int t1
//       3:   | t1 = t0 < 10
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L10
//       6:   | int t2
//       7:   | t2 = t0
//       8:   | t2 = t2 + 1
//       9:   | jmp L2
//      10:   ret 0
int main() {
    for (int i = 0; i < 10;) {
        int j = i;
        ++j;
    }
    return 0;
}