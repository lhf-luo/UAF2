# 编译器定义
CXX = g++
CXXFLAGS = -g $(shell llvm-config-13 --cxxflags) -std=c++17 -fexceptions
LDFLAGS = $(shell llvm-config-13 --ldflags --libs --system-libs all)

# 路径定义
SRC_DIR = lib
BUILD_DIR = build
TARGET = $(BUILD_DIR)/analyzer

# 自动获取所有的 .cc 文件并转换为 .o 文件路径
SRCS = $(wildcard $(SRC_DIR)/*.cc)
OBJS = $(patsubst $(SRC_DIR)/%.cc, $(BUILD_DIR)/%.o, $(SRCS))

# 默认目标
all: $(TARGET)

# 链接阶段：只有当 .o 文件更新时才执行
$(TARGET): $(OBJS)
	@mkdir -p $(BUILD_DIR)
	$(CXX) $(OBJS) -o $(TARGET) $(LDFLAGS)

# 编译阶段：针对每个 .cc 文件生成 .o 文件
# -c 参数表示只编译不链接，这是实现增量编译的核心
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cc
	@mkdir -p $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -rf $(BUILD_DIR)/*.o $(TARGET)