//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | int t1
//       3:   | t1 = t0 < 10
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L17
//       6:   | int t2
//       7:   | t2 = 10
//       8:   | | int t3
//       9:   | | t3 = t2 >= 0
//      10:   | | if t3 != 0 goto L12
//      11:   | | jmp L15
//      12:   | | t0 = t0 - 1
//      13:   | | t2 = t2 - 1
//      14:   | | jmp L8
//      15:   | t0 = t0 + 1
//      16:   | jmp L2
//      17:   ret 0
//--------
//  0: cfg = 0, next = (1)
//  1: cfg = 1, prev = (0), next = (2)
//  2: cfg = 1, prev = (1, 16), next = (3)
//  3: cfg = 2, prev = (2), next = (4)
//  4: cfg = 2, prev = (3), next = (6, 5)
//  5: cfg = 3, prev = (4), next = (17)
//  6: cfg = 4, prev = (4), next = (7)
//  7: cfg = 4, prev = (6), next = (8)
//  8: cfg = 4, prev = (7, 14), next = (9)
//  9: cfg = 5, prev = (8), next = (10)
// 10: cfg = 5, prev = (9), next = (12, 11)
// 11: cfg = 6, prev = (10), next = (15)
// 12: cfg = 7, prev = (10), next = (13)
// 13: cfg = 7, prev = (12), next = (14)
// 14: cfg = 7, prev = (13), next = (8)
// 15: cfg = 8, prev = (11), next = (16)
// 16: cfg = 8, prev = (15), next = (2)
// 17: cfg = 9, prev = (5)
int main() {
    for (int i = 0; i < 10; ++i) {
        for (int j = 10; j >= 0; --j) {
            --i;
        }
    }
    return 0;
}