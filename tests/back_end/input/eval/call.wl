//9
int f(int arg) {
    return arg + 1;
}

int g(int arg) {
    return f(f(arg));
}

int main() {
    return g(g(g(g(1))));
}