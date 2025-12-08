package com.beemediate.beemediate.controller.http;

import org.junit.Before;
import org.junit.Test;
import org.mockito.Mockito;
import org.springframework.http.MediaType;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;

import com.beemediate.beemediate.controller.http.impl.ManagerRestController;
import com.beemediate.beemediate.domain.ports.controller.OaFManagerPort;

// --- IMPORT STATICI FONDAMENTALI ---
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.times;
import static org.mockito.ArgumentMatchers.any;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
// Se i metodi sono mappati come POST, usa: import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.post;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.content;

public class ManagerRestControllerTest {

    private MockMvc mockMvc;
    private OaFManagerPort oafManagerPortMock;

    @Before
    public void setUp() {

        oafManagerPortMock = Mockito.mock(OaFManagerPort.class);


        ManagerRestController controller = new ManagerRestController(oafManagerPortMock);


        this.mockMvc = MockMvcBuilders.standaloneSetup(controller).build();
    }

    // --- TEST CHECK HEALTH ---

    @Test
    public void testCheckHealth() throws Exception {

        String url = "/manage/healthcheck"; 

        mockMvc.perform(get(url))
                .andExpect(status().isOk())
                .andExpect(content().string("Backend attiva"));
    }

    // --- TEST MANAGE ORDERS ---

    @Test
    public void testManageOrders_Success() throws Exception {

        String url = "/manage/orders"; 
        
        when(oafManagerPortMock.handleOrders()).thenReturn(5);

        mockMvc.perform(get(url)) 
                .andExpect(status().isOk())
                .andExpect(content().string("Processed 5 orders."));

        verify(oafManagerPortMock, times(1)).handleOrders();
    }

    @Test
    public void testManageOrders_Exception() throws Exception {
        String url = "/manage/orders";
        
        when(oafManagerPortMock.handleOrders()).thenThrow(new RuntimeException("DB connection failed"));

        mockMvc.perform(get(url))
                .andExpect(status().isInternalServerError()) // Verifica HTTP 500
                .andExpect(content().string("Error while processing orders: DB connection failed"));
    }

    // --- TEST MANAGE CONFIRMATIONS ---

    @Test
    public void testManageConfirmations_Success() throws Exception {

        String url = "/manage/confirmations";

        when(oafManagerPortMock.handleConfirmations()).thenReturn(12);

        mockMvc.perform(get(url))
                .andExpect(status().isOk())
                .andExpect(content().string("Processed 12 confirmations."));
        
        verify(oafManagerPortMock, times(1)).handleConfirmations();
    }

    @Test
    public void testManageConfirmations_Exception() throws Exception {
        String url = "/manage/confirmations";


        when(oafManagerPortMock.handleConfirmations()).thenThrow(new RuntimeException("Critical Error"));

        mockMvc.perform(get(url))
                .andExpect(status().isInternalServerError()) // Verifica HTTP 500
                .andExpect(content().string("Error while processing confirmations: Critical Error"));
    }
}