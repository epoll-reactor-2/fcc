//fun main():
//       0:   | int t0
//       1:   | int t1
//       2:   | t1 = 2 + 3
//       3:   | t0 = 1 + t1
//       4:   | if t0 != 0 goto L6
//       5:   | jmp L10
//       6:   | ret 1
//       7:   | ret 1
//       8:   | ret 1
//       9:   | jmp L13
//      10:   | ret 2
//      11:   | ret 2
//      12:   | ret 2
//      13:   ret 3
int main() {
    if (1 + 2 + 3) {
        return 1;
        return 1;
        return 1;
    } else {
        return 2;
        return 2;
        return 2;
    }
    return 3;
}