echo "Running pre-commit hook..."
# doxygen
find lib -regextype posix-extended -regex ".*\.[hc]pp" | xargs clang-format -i
git add --update
