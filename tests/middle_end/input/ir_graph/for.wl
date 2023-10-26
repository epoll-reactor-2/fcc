//fun main():
//       0:   int t0(@loop)
//       1:   t0 = 0(@loop)
//       2:   | int t1
//       3:   | t1 = t0 < 10
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L11
//       6:   | int t2
//       7:   | t2 = t0
//       8:   | t2 = t2(@noalias) + 1
//       9:   | t0 = t0(@noalias) + 1(@loop)
//      10:   | jmp L2
//      11:   ret 0
int main() {
    for (int i = 0; i < 10; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}