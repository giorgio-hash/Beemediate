package com.beemediate.beemediate.controller.http;

import org.junit.Before;
import org.junit.Test;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;

import com.beemediate.beemediate.controller.http.impl.UIController;


import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.view;


public class UIControllerTest {

    private MockMvc mockMvc;

    @Before
    public void setUp() {
        UIController uiController = new UIController();
        this.mockMvc = MockMvcBuilders.standaloneSetup(uiController).build();
    }

    @Test
    public void testGetUI_ReturnsCorrectViewName() throws Exception {
        String urlTemplate = "/"; 

        this.mockMvc.perform(get(urlTemplate))
                .andExpect(status().isOk())
                .andExpect(view().name("beemediate-ui.html"));
    }
}