import os
import time
from art import text2art

# Màu sắc cho giao diện console
BLUE = '\x1b[94m'
RED = '\x1b[91m'
RESET = '\x1b[0m'

# Hàm tải `user_id` từ file `config.txt`
def load_user_id():
    try:
        with open("config.txt", "r") as config_file:
            return config_file.read().strip()
    except FileNotFoundError:
        return None

# Hàm lưu `user_id` vào file `config.txt`
def save_user_id(user_id):
    with open("config.txt", "w") as config_file:
        config_file.write(user_id)

# Hàm kiểm tra nếu đang chạy trên Termux
def is_termux_running():
    return os.getenv("TERMUX_VERSION") is not None

# Hàm tự động rejoin vào game
def auto_rejoin(user_id, place_id, sleep_minutes):
    first_run = True  # Biến xác định lần đầu chạy
    while True:
        if not first_run:  # Nếu không phải lần đầu, thực hiện sleep
            print(f"Đợi {sleep_minutes} phút trước khi rejoin...")
            time.sleep(sleep_minutes * 60)  # Chuyển đổi phút sang giây
        else:
            first_run = False  # Sau lần chạy đầu tiên, đặt thành False
        
        print("Đang thực hiện rejoin...")
        if is_termux_running():
            if place_id.startswith("http"):
                os.system(f'am start -a android.intent.action.VIEW -d "{place_id}"')
            else:
                os.system(f'am start -a android.intent.action.VIEW -d "roblox://placeID={place_id}"')
        else:
            os.system("am start -n com.termux/.TermuxActivity")
        print("Đã thực hiện rejoin.")

# Hàm cho người dùng chọn game
def select_game():
    print("Chọn game:")
    print("1 - Blox Fruit")
    print("2 - King Legacy")
    print("3 - Meme Sea")
    print("4 - The Strongest Battleground")
    print("5 - PLS DONATE")
    print("6 - Pet Simulator")
    print("7 - Anime Defender")
    print("8 - Private Server Link")

    choice = input("Nhập số game bạn muốn rejoin: ")
    game_ids = {
        "1": "2753915549",
        "2": "4520749081",
        "3": "10260193230",
        "4": "10449761463",
        "5": "8737602449",
        "6": "6284583030",
        "7": "17017769292"
    }
    if choice in game_ids:
        return game_ids[choice]
    elif choice == "8":
        return input("Nhập link Private Server: ")
    else:
        print("Lựa chọn không hợp lệ, vui lòng thử lại.")
        return select_game()

# Điểm khởi đầu chương trình
if __name__ == "__main__":
    print(BLUE + text2art("Linear Rejoin") + RESET)
    print(RED + "Bản quyền thuộc về Dawn và Linear" + RESET)

    user_id = load_user_id()
    if not user_id:
        user_id = input("Nhập user_id Roblox của bạn: ")
        save_user_id(user_id)
        print("Đã lưu user_id vào config.txt")

    place_id = select_game()

    # Người dùng chọn thời gian chờ
    while True:
        try:
            sleep_minutes = int(input("Nhập thời gian chờ (phút) trước khi rejoin: "))
            if sleep_minutes > 0:
                break
            else:
                print("Thời gian chờ phải lớn hơn 0.")
        except ValueError:
            print("Vui lòng nhập một số nguyên.")

    auto_rejoin(user_id, place_id, sleep_minutes)