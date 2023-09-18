//fun main():
//       0:   alloca [2 x int] %0
//       1:   store %0[$0] $1
//       2:   store %0[$1] $0
//       3:   alloca int %1
//       4:   store %1 %0[$0] add %0[$1]
//       5:   ret %1
int main() {
    int mem_1[2];
    mem_1[0] = 1;
    mem_1[1] = 0;
    return mem_1[0] + mem_1[1];
}