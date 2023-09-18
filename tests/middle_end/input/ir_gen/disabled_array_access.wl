//fun main():
//       0:   alloca [2 x int] %0
//       2:   ret $0
int main() {
    int mem_1[2];
    mem_1[0] = 1;
    mem_1[1] = 0;
    return mem_1[0] + mem_1[1];
}