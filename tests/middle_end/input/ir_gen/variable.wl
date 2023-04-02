//fun main():
//       0:   alloca int %0
//       1:   store %0 $1
//       2:   alloca int %1
//       3:   store %1 $2
//       4:   alloca int %2
//       5:   store %2 $3
//       6:   alloca int %3
//       7:   alloca int %4
//       8:   store %4 %1 add %2
//       9:   store %3 %0 add %4
//      10:   ret %3
int main() {
    int a = 1;
    int b = 2;
    int c = 3;
    return a + b + c;
}