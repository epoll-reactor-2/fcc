//fun unreachable():
//       0:   ret
//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   | int t1(@loop)
//       3:   | t1 = t0 < 10(@loop)
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L26
//       6:   | | int t2
//       7:   | | t2 = t0 % 2
//       8:   | | if t2 != 0 goto L10
//       9:   | | jmp L13
//      10:   | | t0 = t0(@noalias) - 1
//      11:   | | ret 1
//      13:   | | int t3
//      14:   | | t3 = t0 == 5
//      15:   | | if t3 != 0 goto L17
//      16:   | | jmp L22
//      17:   | | ret 0
//      22:   | t0 = t0(@noalias) + 1
//      23:   | ret 2
//      26:   ret 3
void unreachable() {}

int main() {
    int result = 1;

    while (result < 10) {
        if (result % 2) {
            --result;
            return 1;
            unreachable();
        }
        if (result == 5) {
            return 0;
            result = result * 1024;
            unreachable();
        }
        ++result;
        return 2;
        unreachable();
    }

    return 3;
}