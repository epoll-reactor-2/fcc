//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 1
//       4:   int t2
//       5:   int t3
//       6:   t3 = t0 + t1
//       7:   t2 = t3
//       8:   int t4
//       9:   t4 = t0
//      10:   int t5
//      11:   t5 = 9
//      12:   int t6
//      13:   t6 = 8
//      14:   int t7
//      15:   int t8
//      16:   int t9
//      17:   t9 = t0 + t1
//      18:   t8 = t5 + t9
//      19:   t7 = t6 + t8
//      20:   ret t7
//--------
//symbol  0 : reg 0
//symbol  1 : reg 1
//symbol  3 : reg 3
//symbol  2 : reg 2
//symbol  4 : reg 2
//symbol  5 : reg 2
//symbol  6 : reg 3
//symbol  9 : reg 4
//symbol  8 : reg 1
//symbol  7 : reg 0
int main() {
	int a = 0;
	int b = 1;
	int c = a + b;
	int d = a;
	int e = 9;
	int f = 8;
	return f + e + a + b;
}