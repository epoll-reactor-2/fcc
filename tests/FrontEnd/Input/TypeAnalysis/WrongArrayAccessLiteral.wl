// Error at line 4, column 14: Expected integer as array index, got <CHAR>
int main() {
    int array[100];
    array['c'] = 0;
    return 0;
}