// Error at line 4, column 14: Expected integer as array index, got char
int main() {
    int array[100];
    array['c'] = 0;
    return 0;
}