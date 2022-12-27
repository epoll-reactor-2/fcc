// 1
int main() {
	int result = 1000;
	for (int i = 0; i < 1000; ++i) {
		++result;
	}
	return result == 2000;
}
