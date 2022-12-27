// 33
void change(int *mem) {
    mem[0] = 11;
    mem[1] = 22;
}

int main() {
    int mem[2];
    mem[0] = 1;
    mem[1] = 1;
    change(mem);
    return mem[0] + mem[1];
}
