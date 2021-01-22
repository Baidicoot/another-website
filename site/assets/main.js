const images = document.getElementsByTagName("img");

for (let i = 0; i < images.length; i++) {
    images.item(i).onclick = (_) => {
        window.location.href = images.item(i).src;
    }
    /*
    images.item(i).onmouseover = (_) => {
        let alt = images.item(i).alt;
        if (alt === "") {
            return;
        }
        let elem = document.createElement("p");
        elem.innerHTML = alt;
        elem.className = "desc";
        images.item(i).insertAdjacentElement('afterend', elem);
    }

    images.item(i).onmouseout = (_) => {
        let elems = document.getElementsByClassName("desc");
        for (let i = 0; i < elems.length; i++) {
            elems.item(i).parentNode.removeChild(elems.item(i));
        }
    }
    */
}