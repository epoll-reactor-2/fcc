// 100
int sum_of_two(int mem[2]) {
    return mem[0] + mem[1];
}

int main() {
    int mem[2];
    mem[0] = 66;
    mem[1] = 34;
    return sum_of_two(mem);
}