//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   | int t1
//       3:   | int t2
//       4:   | t2 = t0 < 10
//       5:   | int t3
//       6:   | t3 = t0 != 0
//       7:   | t1 = t2 && t3
//       8:   | if t1 != 0 goto L10
//       9:   | jmp L15
//      10:   | int t4
//      11:   | t4 = t0
//      12:   | t4 = t4 + 1
//      13:   | t0 = t0 + 1
//      14:   | jmp L2
//      15:   ret 0
int main() {
    int i = 1;
    while (i < 10 && i != 0) {
        int j = i;
        ++j;
        ++i;
    }
    return 0;
}