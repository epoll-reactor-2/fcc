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
//  0: cfg = 0, next = (2, 1)
//  1: cfg = 1, prev = (0), next = (5)
//  2: cfg = 2, prev = (0), next = (3)
//  3: cfg = 2, prev = (2), next = (4)
//  4: cfg = 2, prev = (3), next = (7)
//  5: cfg = 3, prev = (1), next = (6)
//  6: cfg = 3, prev = (5), next = (7)
//  7: cfg = 3, prev = (4, 6)
int main() {
    if (0) {
        int i = 1;
    } else {
        int i = 2;
    }
    return 0;
}