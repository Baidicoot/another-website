const images = document.getElementsByTagName("img");

for (let i = 0; i < images.length; i++) {
    images.item(i).onclick = (_) => {
        window.location.href = images.item(i).src;
    }
}