//fun main():
//       0:   int t0
//       1:   t0 = 5
//       2:   | if t0 != 0 goto L4
//       3:   | jmp L11
//       4:   | int t1
//       5:   | t1 = 10
//       6:   | | if t1 != 0 goto L8
//       7:   | | jmp L9
//       8:   | | jmp L6
//       9:   | t0 = t0(@noalias) - 1
//      10:   | jmp L2
//      11:   ret t0
//--------
//  0: cfg = 0, next = (1)
//  1: cfg = 1, prev = (0), next = (2)
//  2: cfg = 1, prev = (1, 10), next = (4, 3)
//  3: cfg = 2, prev = (2), next = (11)
//  4: cfg = 3, prev = (2), next = (5)
//  5: cfg = 3, prev = (4), next = (6)
//  6: cfg = 3, prev = (5, 8), next = (8, 7)
//  7: cfg = 4, prev = (6), next = (9)
//  8: cfg = 5, prev = (6), next = (6)
//  9: cfg = 6, prev = (7), next = (10)
// 10: cfg = 6, prev = (9), next = (2)
// 11: cfg = 7, prev = (3)
int main() {
    int i = 5;
    while (i) {
        int j = 10;
        while (j)
            {}
        --i;
    }
    return i;
}