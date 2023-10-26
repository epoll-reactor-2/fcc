//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | int t1(@loop)
//       3:   | t1 = t0 < 10(@loop)
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L11
//       6:   | int t2
//       7:   | t2 = t0
//       8:   | t2 = t2(@noalias) + 1
//       9:   | t0 = t0(@noalias) + 1
//      10:   | jmp L2
//      11:   ret 0
int main() {
    int i = 0;
    while (i < 10) {
        int j = i;
        ++j;
        ++i;
    }
    return 0;
}