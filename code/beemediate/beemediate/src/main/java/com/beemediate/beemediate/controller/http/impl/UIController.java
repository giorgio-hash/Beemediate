package com.beemediate.beemediate.controller.http.impl;

import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;

import com.beemediate.beemediate.controller.http.UIControllerIF;

/**
 * Controller per restituire view
 */
@Controller
public class UIController implements UIControllerIF{

    @Override
    public String getUI(Model model) {
        // Restituisce la pagina HTML statica
        return "beemediate-ui.html";
    }
}
