//fun main():
//       0:   alloca [2 x int] %0
//       1:   alloca int* %1
//       2:   store %1 %0 add $0
//       3:   store *%1 $1
//       4:   alloca int* %2
//       5:   store %2 %0 add $1
//       6:   store *%2 $0
//       7:   alloca int %3
//       8:   alloca int* %4
//       9:   store %4 %0 add $0
//      10:   alloca int* %5
//      11:   store %5 %0 add $1
//      12:   store %3 *%4 add *%5
//      13:   ret %3
int main() {
    int mem_1[2];
    mem_1[0] = 1;
    mem_1[1] = 0;
    return mem_1[0] + mem_1[1];
}