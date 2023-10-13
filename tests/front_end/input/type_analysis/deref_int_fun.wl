//E<7:12>: Attempt to dereference integral type
int c() {
    return 1;
}

int main() {
    return *c();
}