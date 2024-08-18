//fun main():
//       0:   int #reg0
//       4:   int #reg2
//       8:   int #reg2
//       9:   int #reg3
//      10:   int #reg2
//      11:   int #reg3
//      19:   int #reg2
//       2:   int #reg1
//       1:   #reg0 = 0
//       3:   #reg1 = 0
//       5:   | #reg2 = #reg1 >= #reg0
//       6:   | if #reg2 != 0 goto L12
//       7:   | jmp L20
//      12:   | #reg3 = 32 << 2
//      13:   | #reg2 = 23 & #reg3
//      14:   | #reg3 = #reg0 & #reg2
//      15:   | #reg2 = #reg3 | 5
//      16:   | #reg1 = #reg2
//      17:   | #reg0 = #reg0 - 1
//      18:   | jmp L5
//      20:   #reg2 = #reg0 + #reg1
//      21:   ret #reg2
int main() {
	int a = 0;
	int b = 0;

	while (b >= a) {
		b = (a & 23 & 32 << 2) | 5;
		--a;
	}

	return a + b;
}