//fun main():
//       0:   | if 0 != 0 goto L2
//       1:   | jmp L5
//       2:   | int t0
//       3:   | t0 = 1
//       4:   | jmp L7
//       5:   | int t1
//       6:   | t1 = 2
//       7:   ret 0
//--------
//prev(1) = 0
//prev(2) = 0
//prev(3) = 2
//prev(4) = 3
//prev(5) = 1
//prev(6) = 5
//prev(7) = 4, 6
int main() {
    if (0) {
        int i = 1;
    } else {
        int i = 2;
    }
    return 0;
}