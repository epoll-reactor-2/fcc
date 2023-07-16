//6
int plus_one(int a) {
    return a + 1;
}

int f(int a, int b, int c) {
    return plus_one(a) +
           plus_one(b) +
           plus_one(c);
} 

int main() {
    return f(1, 2, 3) + f(4, 5, 6);
}