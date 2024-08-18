//fun main():
//       0:   int #reg0
//       4:   int #reg2
//       5:   int #reg3
//       8:   int #reg2
//      10:   int #reg2
//      12:   int #reg3
//      14:   int #reg0
//      15:   int #reg1
//      16:   int #reg4
//       2:   int #reg1
//       1:   #reg0 = 0
//       3:   #reg1 = 1
//       6:   #reg3 = #reg0 + #reg1
//       7:   #reg2 = #reg3
//       9:   #reg2 = #reg0
//      11:   #reg2 = 9
//      13:   #reg3 = 8
//      17:   #reg4 = #reg0 + #reg1
//      18:   #reg1 = #reg2 + #reg4
//      19:   #reg0 = #reg3 + #reg1
//      20:   ret #reg0
int main() {
	int a = 0;
	int b = 1;
	int c = a + b;
	int d = a;
	int e = 9;
	int f = 8;
	return f + e + a + b;
}